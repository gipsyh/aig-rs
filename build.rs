extern crate cc;

use std::process::Command;

fn main() -> Result<(), String> {
    Command::new("git")
        .args(["submodule", "update", "--init"])
        .status()
        .expect("Failed to update submodules.");

    println!("cargo:rerun-if-changed=./aiger");

    cc::Build::new()
        .include("aiger")
        .file("aiger/aiger.c")
        .opt_level(3)
        .warnings(false)
        .compile("aiger");

    Ok(())
}
