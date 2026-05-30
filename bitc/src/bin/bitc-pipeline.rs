//! Print the LLVM normalization pipeline (`phases` or raw `opt` string).

use std::io::{self, Write};
use std::process;

fn usage() -> ! {
    eprintln!("usage: bitc-pipeline <phases|opt>");
    process::exit(2);
}

fn print_phases(mut out: impl Write) -> io::Result<()> {
    for (i, phase) in bitc::PHASES.iter().enumerate() {
        writeln!(out, "{}. {}", i + 1, phase.title)?;
        for pass in phase.passes {
            if pass.blurb.is_empty() {
                writeln!(out, "   - {}", pass.name)?;
            } else {
                writeln!(out, "   - {} — {}", pass.name, pass.blurb)?;
            }
        }
        writeln!(out)?;
    }
    writeln!(out, "opt -passes={}", bitc::NORMALIZE_PASS_PIPELINE)?;
    Ok(())
}

fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("phases") => {
            if let Err(e) = print_phases(io::stdout()) {
                eprintln!("bitc-pipeline: {e}");
                process::exit(1);
            }
        }
        Some("opt") => {
            println!("{}", bitc::NORMALIZE_PASS_PIPELINE);
        }
        _ => usage(),
    }
}
