//! DIMACS module responsible for parsing DIMACS CNF problem files.
use crate::literal::{Polarity, VariableIdx};
use crate::manager::SddManager;
use crate::sdd::SddRef;

use anyhow::{bail, Result};

/// Preamble of the DIMACS file.
#[derive(Debug, PartialEq, Eq)]
pub struct Preamble {
    pub clauses: usize,
    pub variables: usize,
}

/// Single clause -- disjunction of literals.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Clause {
    pub(crate) var_label_polarities: Vec<Polarity>,
    pub(crate) var_label_indices: Vec<u32>,
}

impl Clause {
    #[must_use]
    pub(crate) fn to_sdd(&self, manager: &SddManager) -> SddRef {
        let mut sdd = manager.contradiction();

        for (idx, polarity) in self
            .var_label_indices
            .iter()
            .zip(self.var_label_polarities.iter())
        {
            // DIMACS variables are indexed from 1 but our variables start at 0.
            let lit = manager.literal_from_idx(VariableIdx(idx - 1), *polarity);
            sdd = manager.disjoin(&sdd, &lit);
        }

        sdd
    }
}

/// Current state of the DIMACS reader.
#[derive(PartialEq, Eq)]
enum DimacsParserState {
    Initialized,
    PreambleParsed,
    ParsingClauses,
    Finished,
}

/// DIMACS parser.
#[allow(clippy::module_name_repetitions)]
pub struct DimacsParser<'a> {
    reader: &'a mut dyn std::io::BufRead,
    state: DimacsParserState,
}

impl<'a> DimacsParser<'a> {
    #[must_use]
    pub fn new(reader: &'a mut dyn std::io::BufRead) -> Self {
        DimacsParser {
            state: DimacsParserState::Initialized,
            reader,
        }
    }

    /// Parse preamble of the DIMACS file.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// * the preamble has already been parsed,
    /// * the preamble is missing a 'problem line',
    /// * could not skip over comments in the preamble
    /// * could not parse a 'problem line'
    pub fn parse_preamble(&mut self) -> Result<Preamble> {
        if self.state != DimacsParserState::Initialized {
            bail!("preamble already parsed");
        }

        // Consume comments and advance to the problem line.
        while match peek_line(self.reader).get(0..1) {
            None => bail!("preamble is missing a problem line"),
            Some(first_char) => first_char == "c",
        } {
            let mut buf = String::new();
            match self.reader.read_line(&mut buf) {
                Ok(..) => {}
                Err(err) => bail!("could not parse preamble comment: {err}"),
            }
        }

        let mut problem = String::new();
        match self.reader.read_line(&mut problem) {
            Ok(..) => self.parse_problem_line(problem.trim()),
            Err(err) => bail!("could not parse problem line: {err}"),
        }
    }

    /// Parse the next clause.
    pub(crate) fn parse_next_clause(&mut self) -> Result<Option<Clause>> {
        assert!(self.state != DimacsParserState::Initialized);

        if self.state == DimacsParserState::Finished {
            return Ok(None);
        }

        let mut clause = String::new();
        match self.reader.read_line(&mut clause) {
            Ok(read) => {
                if read == 0 {
                    self.state = DimacsParserState::Finished;
                    Ok(None)
                } else {
                    self.state = DimacsParserState::ParsingClauses;
                    let clause = clause.trim().to_owned();
                    if clause == "%" {
                        let mut zero = String::new();
                        let _ = self.reader.read_line(&mut zero);
                        if zero.trim() == "0" {
                            return Ok(None);
                        }
                        bail!("expected '0' after '%' but found '{zero}' instead");
                    }

                    DimacsParser::parse_clause_line(&clause)
                }
            }
            Err(err) => bail!("could not parse clause: {err}"),
        }
    }

    fn parse_problem_line(&mut self, line: &str) -> Result<Preamble> {
        let items: Vec<_> = line
            .split(' ')
            .filter(|element| !element.trim().is_empty())
            .collect();
        if items.len() != 4 {
            bail!("problem line must contain exactly 4 fields: 'p cnf VARIABLES CLAUSES'");
        }

        if *items.first().unwrap() != "p" {
            bail!("first field of problem line must be 'p'");
        }

        if *items.get(1).unwrap() != "cnf" {
            bail!("second field of problem line must be 'cnf'");
        }

        let variables = match items.get(2).unwrap().parse::<usize>() {
            Ok(variables) => variables,
            Err(err) => bail!("could not parse number of variables: {err}"),
        };

        let clauses = match items.get(3).unwrap().parse::<usize>() {
            Ok(variables) => variables,
            Err(err) => bail!("could not parse number of clauses: {err}"),
        };

        self.state = DimacsParserState::PreambleParsed;
        Ok(Preamble { clauses, variables })
    }

    fn parse_clause_line(line: &str) -> Result<Option<Clause>> {
        let tokens: Vec<_> = line
            .split(' ')
            .filter(|token| *token != "0" && token.trim() != "")
            .collect();

        let literals: Vec<_> = tokens
            .iter()
            .map(|variable_idx| match variable_idx.trim().parse::<i32>() {
                Err(err) => bail!("literal '{variable_idx}' is invalid: {err}"),
                Ok(idx) => Ok((Polarity::from(!variable_idx.starts_with('-')), idx)),
            })
            .collect();

        // We must have parsed a line that had only a '0'.
        if literals.is_empty() {
            return Ok(None);
        }

        let mut clause = Clause {
            var_label_indices: Vec::new(),
            var_label_polarities: Vec::new(),
        };

        for literal in &literals {
            match literal {
                Ok((polarity, idx)) => {
                    clause.var_label_indices.push(idx.unsigned_abs());
                    clause.var_label_polarities.push(*polarity);
                }
                Err(err) => bail!("could not parse clause: {err}"),
            }
        }

        Ok(Some(clause))
    }
}

#[must_use]
fn peek_line(reader: &mut dyn std::io::BufRead) -> &str {
    std::str::from_utf8(reader.fill_buf().unwrap()).unwrap()
}

#[cfg(test)]
mod test {
    use pretty_assertions::assert_eq;

    use std::io::BufReader;

    use super::{DimacsParser, Preamble};
    use crate::{literal::Polarity, manager::dimacs::Clause};

    fn collect_clauses(dimacs: &mut DimacsParser) -> Vec<Clause> {
        let mut clauses = Vec::new();

        loop {
            match dimacs.parse_next_clause() {
                Ok(Some(clause)) => clauses.push(clause),
                Ok(None) => break,
                Err(err) => panic!("{err}"),
            }
        }

        clauses
    }

    #[test]
    fn dimacs_ok() {
        let contents = "c Example CNF format file
c
p cnf 4 3
1 3 -4 0
4 0
2 -3 0";
        let mut reader = BufReader::new(contents.as_bytes());
        let mut dimacs = DimacsParser::new(&mut reader);

        assert_eq!(
            dimacs.parse_preamble().unwrap(),
            Preamble {
                variables: 4,
                clauses: 3
            }
        );

        let clauses = collect_clauses(&mut dimacs);

        assert_eq!(
            clauses,
            vec![
                Clause {
                    var_label_indices: vec![1, 3, 4],
                    var_label_polarities: vec![
                        Polarity::Positive,
                        Polarity::Positive,
                        Polarity::Negative
                    ],
                },
                Clause {
                    var_label_indices: vec![4],
                    var_label_polarities: vec![Polarity::Positive,],
                },
                Clause {
                    var_label_indices: vec![2, 3],
                    var_label_polarities: vec![Polarity::Positive, Polarity::Negative],
                },
            ]
        );
    }

    #[test]
    fn preamble_with_whitespace() {
        let contents = "c Example CNF format file
c
p   cnf  4   3
1 3 -4 0
4 0 2
-3 0";
        let mut reader = BufReader::new(contents.as_bytes());
        let mut dimacs = DimacsParser::new(&mut reader);

        assert_eq!(
            dimacs.parse_preamble().unwrap(),
            Preamble {
                variables: 4,
                clauses: 3
            }
        );
    }

    #[test]
    fn clauses_with_whitespace() {
        let contents = "c Example CNF format file
c
p cnf 4 2
1  3  -4 0
  4 0
";
        let mut reader = BufReader::new(contents.as_bytes());
        let mut dimacs = DimacsParser::new(&mut reader);

        assert_eq!(
            dimacs.parse_preamble().unwrap(),
            Preamble {
                variables: 4,
                clauses: 2
            }
        );
    }

    #[test]
    fn trailing_eof_syntax() {
        // This weird format with trailing '%\n0\n' is in the SATLIB benchmarks: https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html
        let contents = "c Example CNF format file
c
p cnf 4 2
1 3 -4 0
4 0
%
0
";
        let mut reader = BufReader::new(contents.as_bytes());
        let mut dimacs = DimacsParser::new(&mut reader);

        assert_eq!(
            dimacs.parse_preamble().unwrap(),
            Preamble {
                variables: 4,
                clauses: 2
            }
        );

        let clauses = collect_clauses(&mut dimacs);

        assert_eq!(
            clauses,
            vec![
                Clause {
                    var_label_indices: vec![1, 3, 4],
                    var_label_polarities: vec![
                        Polarity::Positive,
                        Polarity::Positive,
                        Polarity::Negative
                    ],
                },
                Clause {
                    var_label_indices: vec![4],
                    var_label_polarities: vec![Polarity::Positive],
                },
            ]
        );
    }

    #[test]
    fn trailing_zeros() {
        let contents = "c Example CNF format file
c
p cnf 4 2
1 3 -4 0
4 0
";
        let mut reader = BufReader::new(contents.as_bytes());
        let mut dimacs = DimacsParser::new(&mut reader);

        assert_eq!(
            dimacs.parse_preamble().unwrap(),
            Preamble {
                variables: 4,
                clauses: 2
            }
        );

        let clauses = collect_clauses(&mut dimacs);

        assert_eq!(
            clauses,
            vec![
                Clause {
                    var_label_indices: vec![1, 3, 4],
                    var_label_polarities: vec![
                        Polarity::Positive,
                        Polarity::Positive,
                        Polarity::Negative
                    ],
                },
                Clause {
                    var_label_indices: vec![4],
                    var_label_polarities: vec![Polarity::Positive],
                },
            ]
        );
    }
}
