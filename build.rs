extern crate autocfg;

fn main() {
    let ac = autocfg::new();
    ac.emit_expression_cfg("const { _ = &mut (); }", "has_const_mut");
    ac.emit_path_cfg("core::error::Error", "has_core_error");
}
