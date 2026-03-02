#![no_main]

use libfuzzer_sys::fuzz_target;
use ttrpg_ast::FileId;
use ttrpg_interp::Interpreter;

fuzz_target!(|data: &[u8]| {
    let Ok(source) = std::str::from_utf8(data) else {
        return;
    };

    let (program, _parse_diags) = ttrpg_parser::parse(source, FileId::SYNTH);

    let mut lower_diags = Vec::new();
    let program = ttrpg_parser::lower_moves(program, &mut lower_diags);

    let result = ttrpg_checker::check(&program);

    let _interp = Interpreter::new(&program, &result.env);
});
