use crate::literal::Polarity;
use crate::sdd::Sdd;

use super::SddManager;

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Preamble {
    pub(crate) clauses: usize,
    pub(crate) variables: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Clause {
    pub(crate) var_label_polarities: Vec<Polarity>,
    pub(crate) var_label_indices: Vec<u16>,
}

impl Clause {
    #[must_use]
    pub(crate) fn to_sdd(&self, manager: &SddManager) -> Sdd {
        let mut sdd = manager.contradiction();

        for (idx, polarity) in self
            .var_label_indices
            .iter()
            .zip(self.var_label_polarities.iter())
        {
            // DIMACS variables are indexed from 1 but our variables start at 0.
            let lit = manager.literal_from_idx(*idx - 1, *polarity);
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

pub(crate) struct DimacsReader<'a> {
    reader: &'a mut dyn std::io::BufRead,
    state: DimacsReaderState,
}

impl<'a> DimacsReader<'a> {
    #[must_use]
    pub(crate) fn new(reader: &'a mut dyn std::io::BufRead) -> Self {
        DimacsReader {
            state: DimacsReaderState::Initialized,
            reader,
        }
    }

    #[must_use]
    pub(crate) fn parse_preamble(&mut self) -> Result<Preamble, String> {
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
            Ok(..) => self.parse_problem_line(&problem.trim()),
            Err(err) => Err(format!("could not parse problem line: {err}")),
        }
    }

    #[must_use]
    pub(crate) fn parse_next_clause(&mut self) -> Result<Option<Clause>, String> {
        assert!(self.state != DimacsReaderState::Initialized);

        if self.state == DimacsReaderState::Finished {
            return Ok(None);
        }

        let mut clause = vec![];
        match self.reader.read_until(b'0', &mut clause) {
            Ok(read) => {
                if read == 0 {
                    self.state = DimacsReaderState::Finished;
                    Ok(None)
                } else {
                    self.state = DimacsReaderState::ParsingClauses;
                    self.parse_clause_line(&clause).map(|clause| Some(clause))
                }
            }
            Err(err) => return Err(format!("could not parse clause: {err}")),
        }
    }

    #[must_use]
    fn parse_problem_line(&mut self, line: &str) -> Result<Preamble, String> {
        let items: Vec<_> = line.split(" ").collect();
        if items.len() != 4 {
            return Err(String::from(
                "problem line must contain exactly 4 fields: 'p cnf VARIABLES CLAUSES'",
            ));
        }

        if *items.get(0).unwrap() != "p" {
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

    #[must_use]
    fn parse_clause_line(&mut self, line: &[u8]) -> Result<Clause, String> {
        let literals: Vec<_> = line
            .split(|num| *num == b' ' || *num == b'\n')
            .into_iter()
            .filter(|variable| *variable != [b'0'] && *variable != [])
            .map(|variable| {
                let string = String::from_utf8_lossy(variable);
                match string.trim().parse::<i64>() {
                    Err(err) => Err(format!("literal '{string}' is invalid: {err}")),
                    Ok(idx) => Ok((Polarity::from(!string.starts_with("-")), idx)),
                }
            })
            .collect();

        let mut clause = Clause {
            var_label_indices: Vec::new(),
            var_label_polarities: Vec::new(),
        };

        for literal in &literals {
            match literal {
                Ok((polarity, idx)) => {
                    clause.var_label_indices.push(idx.abs() as u16);
                    clause.var_label_polarities.push(*polarity);
                }
                Err(err) => return Err(format!("could not parse clause: {err}")),
            }
        }

        Ok(clause)
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

    use crate::{literal::Polarity, manager::dimacs::Clause};

    use super::{DimacsReader, Preamble};

    #[test]
    fn dimacs_ok() {
        let contents = "c Example CNF format file
c
p cnf 4 3
1 3 -4 0
4 0 2
-3";
        let mut reader = BufReader::new(contents.as_bytes());
        let mut dimacs = DimacsReader::new(&mut reader);

        assert_eq!(
            dimacs.parse_preamble(),
            Ok(Preamble {
                variables: 4,
                clauses: 3
            })
        );

        let mut clauses = Vec::new();

        loop {
            match dimacs.parse_next_clause() {
                Ok(Some(clause)) => clauses.push(clause),
                Ok(None) => break,
                Err(err) => panic!("{err}"),
            }
        }

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
}
