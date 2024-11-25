use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::time::{Duration, Instant};

use clap::{Parser, ValueEnum};
use rsdd::builder::sdd::{CompressionSddBuilder, SddBuilder, SemanticSddBuilder};
use rsdd::builder::BottomUpBuilder;
use rsdd::constants::primes;
use rsdd::repr::{
    Cnf, DDNNFPtr, DTree, SddPtr, VTree, VTreeManager, VarLabel, VarOrder, WmcParams,
};
use rsdd::util::semirings::RealSemiring;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Path to DIMACS file with CNF to construct SDD from
    #[arg(short, long, value_name = "dimacs.cnf")]
    dimacs_path: String,

    /// Vtree configuration.
    #[arg(long, value_enum, default_value_t = VTreeStrategy::RightLinear)]
    vtree: VTreeStrategy,
}

#[derive(Clone, Debug, ValueEnum)]
pub enum VTreeStrategy {
    LeftLinear,
    RightLinear,
    DTreeLinear,
    DTreeMinFill,
}

impl VTreeStrategy {
    fn vtree(&self, variables: &[VarLabel], cnf: &Cnf) -> VTree {
        match self {
            VTreeStrategy::LeftLinear => VTree::left_linear(variables),
            VTreeStrategy::RightLinear => VTree::right_linear(variables),
            VTreeStrategy::DTreeLinear => {
                let dtree = DTree::from_cnf(cnf, &VarOrder::linear_order(cnf.num_vars()));
                VTree::from_dtree(&dtree).unwrap()
            }
            VTreeStrategy::DTreeMinFill => {
                let dtree = DTree::from_cnf(cnf, &cnf.min_fill_order());
                VTree::from_dtree(&dtree).unwrap()
            }
        }
    }
}

struct Statistics {
    name: String,
    compilation_time: Duration,
    compiled_sdd_size: usize,
    model_count: f64,
    model_count_time: Duration,
}

impl Statistics {
    fn print(&self) {
        println!("{}...", self.name);
        println!("compilation time: {:.2?}", self.compilation_time);
        println!("SDD size        : {}", self.compiled_sdd_size);
        println!("models:         : {}", self.model_count);
        println!("model count time: {:.2?}", self.model_count_time);
    }
}

fn model_count_sdd(sdd: &SddPtr, manager: &VTreeManager) -> (f64, Duration) {
    let mut vars = HashMap::new();
    for v in 0..manager.num_vars() + 1 {
        vars.insert(
            VarLabel::new_usize(v),
            (RealSemiring(0.0), RealSemiring(1.0)),
        );
    }

    let params = WmcParams::<RealSemiring>::new(vars);
    let start = Instant::now();
    let model_count = sdd.unsmoothed_wmc(&params);
    (model_count.0, start.elapsed())
}

fn main() -> Result<(), std::io::Error> {
    let args = Cli::parse();
    let mut f = File::open(args.dimacs_path)?;
    let mut dimacs = String::new();
    f.read_to_string(&mut dimacs)?;

    let cnf = Cnf::from_dimacs(&dimacs);
    let range: Vec<usize> = (0..cnf.num_vars()).collect();
    let binding = range
        .iter()
        .map(|i| VarLabel::new(*i as u64))
        .collect::<Vec<VarLabel>>();
    let variables = binding.as_slice();

    let vtree = args.vtree.vtree(variables, &cnf);

    println!("vtree      : {:?}", args.vtree);
    println!("num vars   : {}", cnf.num_vars(),);
    println!("num clauses: {}", cnf.clauses().len());

    let comp_builder = CompressionSddBuilder::new(vtree.clone());
    let comp_compilation_start = Instant::now();
    let comp_sdd = comp_builder.compile_cnf(&cnf);
    let comp_vtree = comp_builder.vtree_manager();
    let (model_count, mc_time) = model_count_sdd(&comp_sdd, comp_vtree);
    Statistics {
        name: String::from("compression builder"),
        compilation_time: comp_compilation_start.elapsed(),
        compiled_sdd_size: comp_sdd.count_nodes(),
        model_count_time: mc_time,
        model_count,
    }
    .print();

    let sem_builder = SemanticSddBuilder::<{ primes::U64_LARGEST }>::new(vtree.clone());
    let sem_compilation_start = Instant::now();
    let sem_sdd = sem_builder.compile_cnf(&cnf);
    let sem_vtree = sem_builder.vtree_manager();
    let (model_count, mc_time) = model_count_sdd(&sem_sdd, sem_vtree);

    Statistics {
        name: String::from("semantic builder"),
        compilation_time: sem_compilation_start.elapsed(),
        compiled_sdd_size: sem_sdd.count_nodes(),
        model_count_time: mc_time,
        model_count,
    }
    .print();

    Ok(())
}
