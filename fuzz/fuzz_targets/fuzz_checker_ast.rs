#![no_main]

use arbitrary::Unstructured;
use libfuzzer_sys::fuzz_target;
use ttrpg_ast::ast::Program;

fuzz_target!(|data: &[u8]| {
    let Ok(program) = Unstructured::new(data).arbitrary::<Program>() else {
        return;
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut diags = Vec::new();
        let program = ttrpg_parser::lower_moves(program, &mut diags);

        let _result = ttrpg_checker::check(&program);
    }));

    if let Err(panic) = result {
        // Re-decode the program for display (the original was moved into the closure)
        if let Ok(program) = Unstructured::new(data).arbitrary::<Program>() {
            eprintln!("=== FAILED AST ===\n{program:#?}\n==================");
        }
        std::panic::resume_unwind(panic);
    }
});
