#![no_main]

use arbitrary::Unstructured;
use libfuzzer_sys::fuzz_target;
use ttrpg_ast::ast::Program;
use ttrpg_interp::Interpreter;

fuzz_target!(|data: &[u8]| {
    let Ok(program) = Unstructured::new(data).arbitrary::<Program>() else {
        return;
    };

    let mut diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut diags);

    let result = ttrpg_checker::check(&program);

    let _interp = Interpreter::new(&program, &result.env);
});
