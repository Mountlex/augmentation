#![feature(drain_filter)]

use std::{fmt::Display, fs::OpenOptions, path::PathBuf};

use clap::Parser;

pub use credit::*;
use num_rational::Rational64;
use path::{prove_nice_path_progress, test_instance};

use comps::*;
use rayon::prelude::{IntoParallelIterator, ParallelIterator};
use tree::prove_tree_case;

mod bridges;
mod util;
//mod contract;
//mod local_merge;
mod comps;
mod credit;
mod path;
mod proof_logic;
mod proof_tree;
mod tree;
mod types;

#[derive(Copy, Clone, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub enum Node {
    Node(u32),
    Comp(u32),
}

impl Node {
    pub fn n(id: u32) -> Self {
        Node::Node(id)
    }
    pub fn c(id: u32) -> Self {
        Node::Comp(id)
    }
    pub fn set_id(&mut self, offset: u32) {
        match self {
            Node::Node(id) => *id = offset,
            Node::Comp(id) => *id = offset,
        }
    }

    pub fn inc_id(&mut self, offset: u32) {
        match self {
            Node::Node(id) => *id += offset,
            Node::Comp(id) => *id += offset,
        }
    }

    pub fn is_comp(&self) -> bool {
        matches!(self, Node::Comp(_))
    }

    pub fn to_vertex(&self) -> u32 {
        match self {
            Node::Node(n) => *n,
            Node::Comp(_) => panic!("Node not a vertex!"),
        }
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Node(n) => write!(f, "{}", n),
            Node::Comp(n) => write!(f, "2ec({})", n),
        }
    }
}

impl From<u32> for Node {
    fn from(n: u32) -> Self {
        Node::Node(n)
    }
}

//pub type Node = u32;
pub type Graph = petgraph::graphmap::UnGraphMap<Node, EdgeType>;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
enum Cli {
    Tree(Tree),
    Path(Path),
    Test,
}

#[derive(Parser)]
struct Tree {
    c_numer: i64,
    c_demon: i64,

    #[clap(short, long, default_value = "proofs_tree")]
    output_dir: PathBuf,

    #[clap(short = 'd', long = "depth", default_value = "2")]
    output_depth: usize,

    #[clap(short, long)]
    parallel: bool,

    #[clap(short, long)]
    sc: bool,
}

#[derive(Parser)]
struct Path {
    c_numer: i64,
    c_demon: i64,

    #[clap(short, long, default_value = "proofs_path")]
    output_dir: PathBuf,

    #[clap(short = 'd', long = "depth", default_value = "2")]
    output_depth: usize,

    #[clap(short, long)]
    parallel: bool,

    #[clap(short, long)]
    sc: bool,
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    setup_logging(false)?;

    match cli {
        Cli::Tree(local) => prove_local(local),
        Cli::Path(path) => prove_path(path),
        Cli::Test => test_instance()
    }

    Ok(())
}

fn prove_local(tree: Tree) {
    let inv = CreditInv::new(Rational64::new(tree.c_numer, tree.c_demon));

    let leaf_comps = vec![large()]; //, complex_tree(), complex_path()];

    let comps = if inv.c < Credit::new(2, 7) {
        vec![
            large(),
            //complex_tree(),
            //complex_path(),
            c3(),
            c4(),
            c5(),
            c6(),
            c7(),
        ]
    } else {
        vec![
            large(),
            //complex_tree(),
            //complex_path(),
            c3(),
            c4(),
            c5(),
            c6(),
        ]
    };

    if tree.parallel {
        leaf_comps.into_par_iter().for_each(|leaf_comp| {
            prove_tree_case(
                comps.clone(),
                leaf_comp,
                &inv,
                tree.output_dir.clone(),
                tree.output_depth,
                tree.sc,
            )
        });
    } else {
        for leaf_comp in leaf_comps {
            prove_tree_case(
                comps.clone(),
                leaf_comp,
                &inv,
                tree.output_dir.clone(),
                tree.output_depth,
                tree.sc,
            )
        }
    }
}

fn prove_path(path: Path) {
    let inv = CreditInv::new(Rational64::new(path.c_numer, path.c_demon));

    let comps = if inv.c < Credit::new(2, 7) {
        vec![
            large(),
            //complex_tree(),
            //complex_path(),
            c3(),
            c4(),
            c5(),
            //c6(),
            //c7(),
        ]
    } else {
        vec![
            large(),
            //complex_tree(),
            //complex_path(),
            c3(),
            c4(),
            c5(),
            c6(),
        ]
    };

    prove_nice_path_progress(
        comps.clone(),
        comps,
        &inv,
        path.output_dir,
        path.output_depth,
        path.sc,
        path.parallel,
    )
}

fn setup_logging(_verbose: bool) -> Result<(), fern::InitError> {
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
