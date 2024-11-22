use std::fs::File;
use std::io::{BufWriter, Error};

use clap::{Parser, ValueEnum};
use sddrs::manager::options::{FragmentHeuristic, MinimizationCutoff};

use sddrs::manager::{
    options::{InitialVTree, SddOptions},
    SddManager,
};

#[derive(Debug, Clone, ValueEnum)]
enum LogLevel {
    TRACE,
    DEBUG,
    INFO,
    WARN,
    NONE,
}

impl LogLevel {
    fn to_trace(&self) -> Option<tracing::Level> {
        Some(match self {
            LogLevel::TRACE => tracing::Level::TRACE,
            LogLevel::DEBUG => tracing::Level::DEBUG,
            LogLevel::INFO => tracing::Level::INFO,
            LogLevel::WARN => tracing::Level::WARN,
            LogLevel::NONE => return None,
        })
    }
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    // TODO: Option<String> ~> Option<std::path::Path>.
    /// Where to store the DOT graph of the compiled SDD
    #[arg(short, long, value_name = "FILE.dot")]
    sdd_dot_path: Option<String>,

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

    /// Initial vtree configuration.
    #[arg(short, long, value_enum, default_value_t = InitialVTree::Balanced)]
    initial_vtree: InitialVTree,

    /// How to pick a fragment for minimizing.
    #[arg(short, long, value_enum, default_value_t = FragmentHeuristic::Root)]
    fragment_search_heuristic: FragmentHeuristic,

    /// Minimize compiled SDD when done compiling.
    #[arg(long)]
    minimize_after_compiling: bool,

    /// Invoke vtree search after every K clauses. 0 means never.
    #[arg(long, default_value_t = 0)]
    minimize_after_k_clauses: usize,

    /// Verbosity level. See `tracing::Level` for more information.
    #[arg(long, value_enum, default_value_t = LogLevel::WARN)]
    verbosity: LogLevel,

    /// Dump statistics.
    dump_statistics: bool,
}

fn main() -> Result<(), std::io::Error> {
    let args = Cli::parse();

    if let Some(level) = args.verbosity.to_trace() {
        tracing_subscriber::fmt().with_max_level(level).init();
    }

    let options = SddOptions::builder()
        .initial_vtree(args.initial_vtree)
        .fragment_heuristic(args.fragment_search_heuristic)
        .minimize_after(args.minimize_after_k_clauses)
        .minimization_cutoff(MinimizationCutoff::None)
        .build();

    let manager = SddManager::new(options);

    let mut f = File::open(args.dimacs_path)?;
    let sdd = match manager.from_dimacs(&mut f, true) {
        Err(err) => {
            return Err(Error::new(
                std::io::ErrorKind::Other,
                format!("could not construct SDD from the DIMACS file: {}", err),
            ));
        }
        Ok(sdd) => {
            if args.count_models {
                println!("{}", manager.model_count(&sdd));
            }

            if args.enumerate_models {
                println!("{}", manager.model_enumeration(&sdd));
            }
            sdd
        }
    };

    if args.minimize_after_compiling {
        let size_before = manager.size(&sdd);
        manager.minimize(
            options.minimization_cutoff,
            options.fragment_heuristic,
            &sdd,
        );
        let size_after = manager.size(&sdd);
        println!("minimized SDD from {size_before} to {size_after} nodes");
    }

    let _ = write_to_file(
        args.sdd_dot_path.as_deref(),
        |writer: &mut dyn std::io::Write| {
            if args.render_all_sdds {
                manager.draw_all_sdds(writer)
            } else {
                manager.draw_sdd(writer, &sdd)
            }
        },
    );

    let _ = write_to_file(
        args.vtree_dot_path.as_deref(),
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
