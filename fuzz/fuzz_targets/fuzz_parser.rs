#![no_main]

use libfuzzer_sys::fuzz_target;
use ttrpg_ast::FileId;

fuzz_target!(|data: &[u8]| {
    let Ok(source) = std::str::from_utf8(data) else {
        return;
    };

    let (_program, _diagnostics) = ttrpg_parser::parse(source, FileId::SYNTH);
    let (_expr, _diags) = ttrpg_parser::parse_expr(source);
});
