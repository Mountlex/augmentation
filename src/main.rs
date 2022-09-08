use std::{fs::OpenOptions, path::PathBuf};

use clap::Parser;

use itertools::Itertools;
use nice_path::prove_nice_path_progress;
use num_rational::Rational64;

use crate::{comps::*, local_merge::TreeCaseProof};

mod bridges;
mod comps;
mod contract;
mod local_merge;
mod nice_path;
mod proof_tree;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
enum Cli {
    Local(Local),
    Path(Path),
}

#[derive(Parser)]
struct Local {
    c_numer: i64,
    c_demon: i64,

    #[clap(short, long, default_value = "0")]
    depth: usize,

    #[clap(short, long)]
    parallel: bool,

    #[clap(short, long, default_value = "proofs_local")]
    output_dir: PathBuf,

    #[clap(short, long, default_value = "false")]
    verbose: bool,
}

#[derive(Parser)]
struct Path {
    c_numer: i64,
    c_demon: i64,

    #[clap(short, long, default_value = "proofs_path")]
    output_dir: PathBuf,
}

pub type Credit = Rational64;

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    setup_logging(false)?;

    match cli {
        Cli::Local(local) => prove_local(local),
        Cli::Path(path) => prove_path(path),
    }

    Ok(())
}

fn prove_local(local: Local) {
    let inv = DefaultCredits::new(Rational64::new(local.c_numer, local.c_demon));
    let leaf_comps = vec![
        ComponentType::Cycle(4),
        ComponentType::Cycle(5),
        ComponentType::Cycle(6),
        ComponentType::Large,
        ComponentType::Complex,
    ];
    let comps = vec![
        ComponentType::Cycle(3),
        ComponentType::Cycle(4),
        ComponentType::Cycle(5),
        ComponentType::Cycle(6),
        ComponentType::Large,
        ComponentType::Complex,
    ];

    println!("========== Proof for c = {} ==========", inv.c);
    let proof1 = TreeCaseProof::new(leaf_comps, comps.clone(), inv.clone(), local.depth);
    proof1.prove(local.parallel, local.output_dir);
}

fn prove_path(path: Path) {
    let inv = DefaultCredits::new(Rational64::new(path.c_numer, path.c_demon));

    let comps = vec![
        //ComponentType::Cycle(3),
        ComponentType::Cycle(4),
        ComponentType::Cycle(5),
        ComponentType::Cycle(6),
        ComponentType::Large,
        ComponentType::Complex,
    ];

    let comps = comps.into_iter().flat_map(|c| c.components()).collect_vec();

    prove_nice_path_progress(comps, inv, path.output_dir)
}

fn setup_logging(verbose: bool) -> Result<(), fern::InitError> {
    let base_config = fern::Dispatch::new();

    // Separate file config so we can include year, month and day in file logs
    let file_config = fern::Dispatch::new()
        .format(|out, message, record| {
            out.finish(format_args!(
                "{}[{}] {}",
                chrono::Local::now().format("[%H:%M:%S]"),
                record.level(),
                message
            ))
        })
        .level(log::LevelFilter::Trace)
        .chain(
            OpenOptions::new()
                .truncate(true)
                .write(true)
                .create(true)
                .open("program.log")?,
        );

    let stdout_config = fern::Dispatch::new()
        .format(|out, message, record| {
            // special format for debug messages coming from our own crate.
            if record.level() > log::LevelFilter::Info && record.target() == "cmd_program" {
                out.finish(format_args!(
                    "---\nDEBUG: {}: {}\n---",
                    chrono::Local::now().format("%H:%M:%S"),
                    message
                ))
            } else {
                out.finish(format_args!(
                    "[{}][{}] {}",
                    chrono::Local::now().format("%H:%M:%S"),
                    record.level(),
                    message
                ))
            }
        })
        .level(log::LevelFilter::Info)
        .chain(std::io::stdout());

    base_config
        .chain(stdout_config)
        .chain(file_config)
        .apply()?;

    Ok(())
}
