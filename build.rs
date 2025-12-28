extern crate cc;

use std::io;

fn main() -> io::Result<()> {
    giputils::build::git_submodule_update()?;
    println!("cargo:rerun-if-changed=./aiger");
    cc::Build::new()
        .include("aiger")
        .file("aiger/aiger.c")
        .opt_level(3)
        .warnings(false)
        .compile("aiger");

    Ok(())
}
