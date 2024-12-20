use std::fs::File;
use std::io::{BufWriter, Seek};
use std::time::{Duration, Instant};

use anyhow::{bail, Context, Result};
use clap::{Parser, ValueEnum};
use sddrs::manager::dimacs::{self};
use sddrs::manager::options::{
    FragmentHeuristic, GarbageCollection, MinimizationCutoff, VTreeStrategy,
};
use sddrs::manager::GCStatistics;
use sddrs::manager::{options::SddOptions, SddManager};

#[derive(Debug, Clone, ValueEnum)]
enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    None,
}

impl LogLevel {
    fn to_trace(&self) -> Option<tracing::Level> {
        Some(match self {
            LogLevel::Trace => tracing::Level::TRACE,
            LogLevel::Debug => tracing::Level::DEBUG,
            LogLevel::Info => tracing::Level::INFO,
            LogLevel::Warn => tracing::Level::WARN,
            LogLevel::None => return None,
        })
    }
}

#[allow(clippy::struct_excessive_bools)]
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    // TODO: Option<String> ~> Option<std::path::Path>.
    /// Where to store the DOT graph of the compiled SDD
    #[arg(short, long, value_name = "FILE.dot")]
    sdd_dot_path: Option<String>,

    /// Where to store the DOT graph of the final `VTree`
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
    #[arg(long, value_enum, default_value_t = VTreeStrategy::RightLinear)]
    vtree: VTreeStrategy,

    /// Minimize compiled SDD when done compiling. An arbitrary fragment
    /// of the vtree is picked and all 12 configurations are then
    /// selectively tried to find the smallest compiled SDD.
    #[arg(short, long)]
    minimize_after_compiling: bool,

    /// Invoke vtree search after every K clauses. 0 means never.
    #[arg(short = 'k', long, default_value_t = 0)]
    minimize_after_k_clauses: usize,

    /// Verbosity level. See `tracing::Level` for more information.
    #[arg(long, value_enum, default_value_t = LogLevel::Warn)]
    verbosity: LogLevel,

    /// Print timing and size statistics.
    #[arg(short, long)]
    print_statistics: bool,

    /// Collect garbage (dead nodes) after every apply operation.
    #[arg(long)]
    collect_garbage: bool,
}

#[derive(Debug, Clone, Default)]
struct Statistics {
    compilation: Option<Duration>,
    minimization: Option<Duration>,
    model_count_time: Option<Duration>,

    compiled_sdd_size: Option<u64>,
    compiled_sdd_size_after_minimization: Option<u64>,
    all_sdds: Option<u64>,

    gc_stats: Option<GCStatistics>,
}

impl Statistics {
    fn print(&self) {
        println!("compilation time: {:.2?}", self.compilation.unwrap());
        if let Some(model_count_time) = self.model_count_time {
            println!("model count time: {model_count_time:.2?}");
        }

        if self.minimization.is_some() {
            println!("minimization time : {:.2?}", self.minimization.unwrap());
            println!(
                "SDD size (before min.): {}",
                self.compiled_sdd_size.unwrap()
            );
            println!(
                "SDD size (after min.) : {}",
                self.compiled_sdd_size.unwrap()
            );
        } else {
            println!("sdd size        : {}", self.compiled_sdd_size.unwrap());
            println!("all sdds        : {}", self.all_sdds.unwrap());
        }

        if let Some(ref gc_stats) = self.gc_stats {
            println!("nodes collected : {}", gc_stats.nodes_collected);
            println!("gc triggered    : {}", gc_stats.gc_triggered);
        }
    }
}

fn main() -> Result<()> {
    let args = Cli::parse();

    if let Some(level) = args.verbosity.to_trace() {
        tracing_subscriber::fmt().with_max_level(level).init();
    }

    let mut f = File::open(&args.dimacs_path)
        .with_context(|| format!("Could not open DIMACS file {}", args.dimacs_path))?;
    let variables = match get_variables(&mut f) {
        Ok(variables) => variables,
        Err(err) => {
            bail!(err.context("could not construct variables for clauses in the DIMACS file"))
        }
    };

    let mut statistics = Statistics::default();
    let options = SddOptions::builder()
        .vtree_strategy(args.vtree)
        .fragment_heuristic(FragmentHeuristic::MostNormalized)
        .minimization_cutoff(MinimizationCutoff::BreakAfterFirstImprovement)
        .minimize_after(args.minimize_after_k_clauses)
        .variables(variables)
        .garbage_collection(if args.collect_garbage {
            GarbageCollection::Automatic
        } else {
            GarbageCollection::Off
        })
        .build();

    let manager = SddManager::new(&options);

    // We have read the preamble already so we have to rewind the cursor to the beginning
    // of the file.
    f.rewind()?;

    let compilation_start = Instant::now();
    let result = manager.from_dimacs(&mut f);
    statistics.compilation = Some(compilation_start.elapsed());

    let sdd = match result {
        Err(err) => bail!(err.context("could not construct SDD from the DIMACS file")),
        Ok(sdd) => sdd,
    };

    statistics.compiled_sdd_size = Some(sdd.size());
    if args.minimize_after_compiling {
        let minimization_start = Instant::now();
        manager.minimize(
            options.minimization_cutoff,
            &options.fragment_heuristic,
            &sdd,
        )?;

        statistics.compiled_sdd_size_after_minimization = Some(sdd.size());
        statistics.minimization = Some(minimization_start.elapsed());
    }

    if args.count_models {
        let model_count_start = Instant::now();
        let model_count = manager.model_count(&sdd);
        statistics.model_count_time = Some(model_count_start.elapsed());
        println!("{model_count}");
    }

    if args.enumerate_models {
        println!("{}", manager.model_enumeration(&sdd));
    }

    if args.collect_garbage {
        statistics.gc_stats = Some(manager.gc_statistics());
    }

    if args.print_statistics {
        statistics.all_sdds = Some(manager.total_sdds());
        statistics.print();
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
        |writer: &mut dyn std::io::Write| manager.draw_vtree(writer),
    );

    Ok(())
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

fn get_variables(reader: &mut dyn std::io::Read) -> Result<Vec<String>> {
    let mut buffer = std::io::BufReader::new(reader);
    let mut dimacs = dimacs::DimacsParser::new(&mut buffer);
    let preamble = dimacs.parse_preamble()?;

    Ok((1..=preamble.variables)
        .map(|idx| idx.to_string())
        .collect())
}
