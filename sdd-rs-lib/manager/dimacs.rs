use crate::literal::{Polarity, VariableIdx};
use crate::manager::SddManager;
use crate::sdd::SddRef;

#[derive(Debug, PartialEq, Eq)]
pub struct Preamble {
    pub clauses: usize,
    pub variables: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Clause {
    pub(crate) var_label_polarities: Vec<Polarity>,
    pub(crate) var_label_indices: Vec<u16>,
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
            let lit = manager.literal_from_idx(&VariableIdx(*idx as u32 - 1), *polarity);
            sdd = manager.disjoin(&sdd, &lit);
        }

        sdd
    }
}

#[derive(PartialEq, Eq)]
enum DimacsReaderState {
    Initialized,
    PreambleParsed,
    ParsingClauses,
    Finished,
}

pub struct DimacsReader<'a> {
    reader: &'a mut dyn std::io::BufRead,
    state: DimacsReaderState,
}

impl<'a> DimacsReader<'a> {
    #[must_use]
    pub fn new(reader: &'a mut dyn std::io::BufRead) -> Self {
        DimacsReader {
            state: DimacsReaderState::Initialized,
            reader,
        }
    }

    pub fn parse_preamble(&mut self) -> Result<Preamble, String> {
        if self.state != DimacsReaderState::Initialized {
            return Err(String::from("preamble already parsed"));
        }

        // Consume comments and advance to the problem line.
        while match peek_line(self.reader).get(0..1) {
            None => return Err(String::from("preamble is missing a problem line")),
            Some(first_char) => first_char == "c",
        } {
            let mut buf = String::new();
            match self.reader.read_line(&mut buf) {
                Ok(..) => {}
                Err(err) => return Err(format!("could not parse preamble comment: {err}")),
            }
        }

        let mut problem = String::new();
        match self.reader.read_line(&mut problem) {
            Ok(..) => self.parse_problem_line(problem.trim()),
            Err(err) => Err(format!("could not parse problem line: {err}")),
        }
    }

    pub(crate) fn parse_next_clause(&mut self) -> Result<Option<Clause>, String> {
        assert!(self.state != DimacsReaderState::Initialized);

        if self.state == DimacsReaderState::Finished {
            return Ok(None);
        }

        let mut clause = String::new();
        match self.reader.read_line(&mut clause) {
            Ok(read) => {
                if read == 0 {
                    self.state = DimacsReaderState::Finished;
                    Ok(None)
                } else {
                    self.state = DimacsReaderState::ParsingClauses;
                    let clause = clause.trim().to_owned();
                    if clause == "%" {
                        let mut zero = String::new();
                        let _ = self.reader.read_line(&mut zero);
                        if zero.trim() == "0" {
                            return Ok(None);
                        }
                        return Err(format!("expected '0' after '%' but found '{zero}' instead"));
                    }

                    self.parse_clause_line(clause)
                }
            }
            Err(err) => Err(format!("could not parse clause: {err}")),
        }
    }

    fn parse_problem_line(&mut self, line: &str) -> Result<Preamble, String> {
        let items: Vec<_> = line
            .split(" ")
            .filter(|element| !element.trim().is_empty())
            .collect();
        if items.len() != 4 {
            return Err(String::from(
                "problem line must contain exactly 4 fields: 'p cnf VARIABLES CLAUSES'",
            ));
        }

        if *items.first().unwrap() != "p" {
            return Err(String::from("first field of problem line must be 'p'"));
        }

        if *items.get(1).unwrap() != "cnf" {
            return Err(String::from("second field of problem line must be 'cnf'"));
        }

        let variables = match items.get(2).unwrap().parse::<usize>() {
            Ok(variables) => variables,
            Err(err) => return Err(format!("could not parse number of variables: {err}")),
        };

        let clauses = match items.get(3).unwrap().parse::<usize>() {
            Ok(variables) => variables,
            Err(err) => return Err(format!("could not parse number of clauses: {err}")),
        };

        self.state = DimacsReaderState::PreambleParsed;
        Ok(Preamble { clauses, variables })
    }

    fn parse_clause_line(&mut self, line: String) -> Result<Option<Clause>, String> {
        let tokens: Vec<_> = line.split(" ").filter(|token| *token != "0").collect();

        let literals: Vec<_> = tokens
            .iter()
            .map(|variable_idx| match variable_idx.trim().parse::<i64>() {
                Err(err) => Err(format!("literal '{variable_idx}' is invalid: {err}")),
                Ok(idx) => Ok((Polarity::from(!variable_idx.starts_with("-")), idx)),
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
                    clause.var_label_indices.push(idx.unsigned_abs() as u16);
                    clause.var_label_polarities.push(*polarity);
                }
                Err(err) => return Err(format!("could not parse clause: {err}")),
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

    use super::{DimacsReader, Preamble};
    use crate::{literal::Polarity, manager::dimacs::Clause};

    fn collect_clauses(dimacs: &mut DimacsReader) -> Vec<Clause> {
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
        let mut dimacs = DimacsReader::new(&mut reader);

        assert_eq!(
            dimacs.parse_preamble(),
            Ok(Preamble {
                variables: 4,
                clauses: 3
            })
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
        let mut dimacs = DimacsReader::new(&mut reader);

        assert_eq!(
            dimacs.parse_preamble(),
            Ok(Preamble {
                variables: 4,
                clauses: 3
            })
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
        let mut dimacs = DimacsReader::new(&mut reader);

        assert_eq!(
            dimacs.parse_preamble(),
            Ok(Preamble {
                variables: 4,
                clauses: 2
            })
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
        let mut dimacs = DimacsReader::new(&mut reader);

        assert_eq!(
            dimacs.parse_preamble(),
            Ok(Preamble {
                variables: 4,
                clauses: 2
            })
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
        let mut dimacs = DimacsReader::new(&mut reader);

        assert_eq!(
            dimacs.parse_preamble(),
            Ok(Preamble {
                variables: 4,
                clauses: 2
            })
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
