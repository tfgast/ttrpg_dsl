#![no_main]

use libfuzzer_sys::fuzz_target;
use ttrpg_ast::FileId;
use ttrpg_lexer::Lexer;

fuzz_target!(|data: &[u8]| {
    let Ok(source) = std::str::from_utf8(data) else {
        return;
    };

    let lexer = Lexer::new(source, FileId::SYNTH);
    let _tokens: Vec<_> = lexer.collect();
});
