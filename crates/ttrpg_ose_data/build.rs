use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    // The ttrpg.toml lives in the ose/ directory at the workspace root.
    let ose_dir = manifest_dir.join("../../ose");
    let manifest_path = ose_dir.join("ttrpg.toml");

    println!(
        "cargo:rerun-if-changed={}",
        manifest_path.canonicalize().unwrap().display()
    );

    let content = fs::read_to_string(&manifest_path).expect("cannot read ose/ttrpg.toml");
    let manifest: toml::Value = content.parse().expect("cannot parse ose/ttrpg.toml");

    let bundles = manifest["bundles"].as_table().unwrap();
    let full = bundles["full"].as_table().unwrap();
    let entry_names = full["entries"].as_array().unwrap();
    let entries = manifest["entries"].as_table().unwrap();

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let dest = out_dir.join("bundled_files.rs");

    let mut code = String::from("const FILES: &[BundledFile] = &[\n");

    for entry_name in entry_names {
        let name = entry_name.as_str().unwrap();
        let entry = entries[name].as_table().unwrap();
        let path = entry["path"].as_str().unwrap();
        let abs_path = ose_dir.join(path).canonicalize().unwrap();

        println!("cargo:rerun-if-changed={}", abs_path.display());

        code.push_str(&format!(
            "    BundledFile {{\n        name: \"{path}\",\n        contents: include_str!(\"{abs}\"),\n    }},\n",
            abs = abs_path.display(),
        ));
    }

    code.push_str("];\n");

    fs::write(&dest, code).expect("cannot write generated file");
}
