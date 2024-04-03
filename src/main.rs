use std::fs::File;
use std::io::BufWriter;

use clap::Parser;

use sddrs::{
    manager::SddManager,
    options::{GcSchedule, InitialVTree, SddOptions, VTreeStrategy},
    Result,
};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Where to store the DOT graph of the compiled SDD
    #[arg(short, long, value_name = "FILE.dot")]
    pub sdd_dot_path: Option<String>,

    /// Where to store the DOT graph of the final VTree
    #[arg(short, long, value_name = "FILE.dot")]
    vtree_dot_path: Option<String>,
}

fn main() {
    let cli = Cli::parse();
    let options = SddOptions::default()
        .set_gc_schedule(GcSchedule::Automatic(1120))
        .set_gc_strategy(VTreeStrategy::Cycle)
        .set_initial_vtree(InitialVTree::Balanced)
        .to_owned();

    let manager = SddManager::new(options, None);

    let _ = write_to_file(
        cli.sdd_dot_path.as_deref(),
        |writer: &mut dyn std::io::Write| manager.draw_sdd_graph(writer),
    );

    let _ = write_to_file(
        cli.vtree_dot_path.as_deref(),
        |writer: &mut dyn std::io::Write| manager.draw_vtree_graph(writer),
    );
}

fn write_to_file(
    path: Option<&str>,
    writer: impl Fn(&mut dyn std::io::Write) -> Result<()>,
) -> Result<()> {
    if let Some(path) = path {
        let f = File::create(path)?;
        let mut b = BufWriter::new(f);
        writer(&mut b as &mut dyn std::io::Write)?;
    };

    Ok(())
}
