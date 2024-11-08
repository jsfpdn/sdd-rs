use crate::{manager::SddManager, sdd::SddRef};
use std::fs::File;
use std::io::BufWriter;

#[macro_export]
macro_rules! btreeset {
    ( $( $x:expr ),* ) => {
        {
            use std::collections::BTreeSet;
            let mut temp_btreeset = BTreeSet::new();
            $(
                temp_btreeset.insert($x);
            )*
            temp_btreeset
        }
    };
}

/// Get indices of bits set to 1 in a number.
pub(crate) fn set_bits_indices(number: usize) -> Vec<usize> {
    let mut indices = Vec::new();
    for n in 0..number.count_ones() + number.count_zeros() {
        if (number >> n & 1) == 1 {
            indices.push(n as usize)
        }
    }

    indices
}

#[allow(unused)]
pub(crate) fn quick_draw(manager: &SddManager, sdd: &SddRef, path: &str) {
    let f = File::create(format!("{path}.dot")).unwrap();
    let mut b = BufWriter::new(f);
    manager
        .draw_sdd(&mut b as &mut dyn std::io::Write, sdd)
        .unwrap();

    let f = File::create(format!("{path}_vtree.dot")).unwrap();
    let mut b = BufWriter::new(f);
    manager
        .draw_vtree_graph(&mut b as &mut dyn std::io::Write)
        .unwrap();
}

#[allow(unused)]
pub(crate) fn quick_draw_all(manager: &SddManager, path: &str) {
    let f = File::create(path).unwrap();
    let mut b = BufWriter::new(f);
    manager
        .draw_all_sdds(&mut b as &mut dyn std::io::Write)
        .unwrap();
}

#[cfg(test)]
mod test {
    use super::set_bits_indices;

    #[test]
    fn indices_set_bits() {
        assert_eq!(set_bits_indices(0b0), vec![]);
        assert_eq!(set_bits_indices(0b1), vec![0]);
        assert_eq!(set_bits_indices(0b10001), vec![0, 4]);
        assert_eq!(set_bits_indices(0b111), vec![0, 1, 2]);
    }
}
