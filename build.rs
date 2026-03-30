use vergen_git2::Emitter;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let git2 = vergen_git2::Git2Builder::all_git()?;

    Emitter::default().add_instructions(&git2)?.emit()?;
    Ok(())
}
