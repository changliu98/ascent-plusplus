#![cfg(test)]

use ascent::ascent;
use crate::assert_rels_eq;
use crate::capture_generic::CaptureContext;

#[test]
fn test_capture_turbofish_usize() {
    // Test the new generic syntax with usize (count of clauses)
    ascent! {
        relation testa(i32);
        relation testb(i32);
        relation result(usize);

        testa(1);
        testb(2);

        result(count) <--
            testa(a),
            testb(b),
            let count = capture!(CaptureContext::<usize>);
    }

    let mut prog = AscentProgram::default();
    prog.run();

    println!("result: {:?}", prog.result);
    assert_rels_eq!(prog.result, [(2,)]);
}

#[test]
fn test_capture_turbofish_bool() {
    // Test the new generic syntax with bool
    ascent! {
        relation testa(i32);
        relation result(usize);

        testa(1);

        result(1) <--
            testa(a),
            if capture!(CaptureContext::<bool>);
    }

    let mut prog = AscentProgram::default();
    prog.run();

    println!("result: {:?}", prog.result);
    assert_rels_eq!(prog.result, [(1,)]);
}

#[test]
fn test_capture_turbofish_vec_tuple() {
    // Test the new generic syntax with Vec<(String, String)>
    ascent! {
        relation testa(i32);
        relation testb(i32, i32);
        relation result(String, String);

        testa(1);
        testb(2, 1);

        result(name, args) <--
            testa(obj1),
            testb(obj2, obj1),
            for (name, args) in capture!(CaptureContext::<Vec<(String, String)>>);
    }

    let mut prog = AscentProgram::default();
    prog.run();

    println!("result: {:?}", prog.result);
    assert_eq!(prog.result.len(), 2);
    // Now we get actual runtime values formatted with Debug, not variable names
    assert!(prog.result.contains(&("testa".to_string(), "(1,)".to_string())));
    assert!(prog.result.contains(&("testb".to_string(), "(2, 1)".to_string())));
}

#[test]
fn test_capture_turbofish_option() {
    // Test the new generic syntax with Option<usize>
    ascent! {
        relation testa(i32);
        relation testb(i32);
        relation result(usize);

        testa(1);
        testb(2);

        result(count) <--
            testa(a),
            testb(b),
            if let Some(count) = capture!(CaptureContext::<Option<usize>>);
    }

    let mut prog = AscentProgram::default();
    prog.run();

    println!("result: {:?}", prog.result);
    assert_rels_eq!(prog.result, [(2,)]);
}

#[test]
fn test_capture_turbofish_string() {
    // Test the new generic syntax with String (reconstructed rule)
    ascent! {
        relation testa(i32);
        relation testb(i32, i32);
        relation result(String);

        testa(1);
        testb(2, 1);

        result(rule_str) <--
            testa(a),
            testb(b, a),
            let rule_str = capture!(CaptureContext::<String>);
    }

    let mut prog = AscentProgram::default();
    prog.run();

    println!("Generated rule string:\n{}", prog.result.iter().next().unwrap().0);

    let rule_str = prog.result.iter().next().unwrap().0.clone();
    assert!(rule_str.contains("result(rule_str)"));
    // Now we get runtime values formatted with Debug
    assert!(rule_str.contains("testa((1,))"));
    assert!(rule_str.contains("testb((2, 1))"));
    assert!(rule_str.contains("let rule_str = capture!"));
}

#[test]
fn test_capture_turbofish_vec_string() {
    // Test the new generic syntax with Vec<String> (just relation names)
    ascent! {
        relation testa(i32);
        relation testb(i32);
        relation testc(i32);
        relation result(String);

        testa(1);
        testb(2);
        testc(3);

        result(name) <--
            testa(a),
            testb(b),
            testc(c),
            for name in capture!(CaptureContext::<Vec<String>>);
    }

    let mut prog = AscentProgram::default();
    prog.run();

    println!("result: {:?}", prog.result);
    assert_eq!(prog.result.len(), 3);
    assert!(prog.result.contains(&("testa".to_string(),)));
    assert!(prog.result.contains(&("testb".to_string(),)));
    assert!(prog.result.contains(&("testc".to_string(),)));
}

#[test]
fn test_capture_mixed_old_and_new_syntax() {
    // Test that old and new syntax can coexist
fn old_style_count(
    rel_names: &[&str],
    _: &[&str],
    _: &[&str],
    _: &[&str],
    _: &[&str],
    _: &str,
    _: &[String],
    _: &[String],
) -> usize {
        rel_names.len()
    }

    ascent! {
        relation testa(i32);
        relation testb(i32);
        relation result1(usize);
        relation result2(usize);

        testa(1);
        testb(2);

        // Old syntax
        result1(count) <--
            testa(a),
            let count = capture!(old_style_count, usize);

        // New syntax
        result2(count) <--
            testb(b),
            let count = capture!(CaptureContext::<usize>);
    }

    let mut prog = AscentProgram::default();
    prog.run();

    println!("result1 (old): {:?}", prog.result1);
    println!("result2 (new): {:?}", prog.result2);

    // Both should work and produce the same result
    assert_rels_eq!(prog.result1, [(1,)]);
    assert_rels_eq!(prog.result2, [(1,)]);
}

#[test]
fn test_capture_turbofish_empty_clauses() {
    // Test with no preceding clauses - use let instead of for
    ascent! {
        relation result(usize);

        result(count) <--
            let count = capture!(CaptureContext::<usize>);
    }

    let mut prog = AscentProgram::default();
    prog.run();

    println!("result: {:?}", prog.result);
    assert_rels_eq!(prog.result, [(0,)]);
}
