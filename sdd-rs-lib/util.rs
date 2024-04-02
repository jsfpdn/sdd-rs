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
