use std::fs::File;
use std::io::{BufWriter, Error};

use clap::Parser;

use sddrs::manager::{
    options::{InitialVTree, SddOptions},
    SddManager,
};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    // TODO: Option<String> ~> Option<std::path::Path>.
    /// Where to store the DOT graph of the compiled SDD
    #[arg(short, long, value_name = "FILE.dot")]
    pub sdd_dot_path: Option<String>,

    /// Where to store the DOT graph of the final VTree
    #[arg(short, long, value_name = "FILE.dot")]
    vtree_dot_path: Option<String>,

    /// Path to DIMACS file with CNF to construct SDD from
    #[arg(short, long, value_name = "dimacs.cnf")]
    dimacs_path: String,

    /// Print all the models in the stdout.
    #[arg(short, long)]
    enumerate_models: bool,

    /// Print count of the models to the stdout.
    #[arg(short, long)]
    count_models: bool,

    /// Draw every SDD in the unique table instead of just
    /// the result of the computation.
    #[arg(short, long)]
    render_all_sdds: bool,
    // Verbosity level. See `tracing::Level` for more information.
    // `tracing::Level::INFO` is the default.
    // #[arg(long, value_enum)]
    // verbosity: Option<tracing::Level>,
}

fn main() -> Result<(), std::io::Error> {
    let cli = Cli::parse();

    let options = SddOptions::default()
        .set_initial_vtree(InitialVTree::Balanced)
        .to_owned();

    let manager = SddManager::new(options);

    let mut f = File::open(cli.dimacs_path)?;
    let sdd = match manager.from_dimacs(&mut f, true) {
        Err(err) => {
            return Err(Error::new(
                std::io::ErrorKind::Other,
                format!("could not construct SDD from the DIMACS file: {}", err),
            ));
        }
        Ok(sdd) => {
            if cli.count_models {
                println!("{}", manager.model_count(&sdd));
            }

            if cli.enumerate_models {
                println!("{}", manager.model_enumeration(&sdd));
            }
            sdd
        }
    };

    let _ = write_to_file(
        cli.sdd_dot_path.as_deref(),
        |writer: &mut dyn std::io::Write| {
            if cli.render_all_sdds {
                manager.draw_all_sdds(writer)
            } else {
                manager.draw_sdd(writer, &sdd)
            }
        },
    );

    let _ = write_to_file(
        cli.vtree_dot_path.as_deref(),
        |writer: &mut dyn std::io::Write| manager.draw_vtree_graph(writer),
    );

    Ok(())
}

fn write_to_file(
    path: Option<&str>,
    writer: impl Fn(&mut dyn std::io::Write) -> Result<(), String>,
) -> Result<(), String> {
    if let Some(path) = path {
        let f = File::create(path).map_err(|err| err.to_string())?;
        let mut b = BufWriter::new(f);
        writer(&mut b as &mut dyn std::io::Write)?;
    };

    Ok(())
}
