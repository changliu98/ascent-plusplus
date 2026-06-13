
use ascent::ascent;

ascent! {
    struct Io;
    relation input(u32, u32);
    relation output(u32, u32);
    relation foo(u32);
    foo(1);
    foo(2);

    await input;
    yield output;

    input(1, 2);
    output(x, y) <-- foo(x), input(x, y);
}

#[test]
fn test_io() {
    let mut prog = Io::default();

    prog.input = vec![(2, 3)].into_iter().collect();
    prog.run();

    assert_eq!(prog.output.len(), 2);
    assert_eq!(prog.input.len(), 0);

    // `output` is cleared each run (`yield`) and `input` after each run (`await`),
    // and the fact `input(1, 2)` re-fires every run. The supplied input must share
    // its first column with a `foo` fact to join — `(2, 5)` joins `foo(2)`, giving
    // output {(1, 2), (2, 5)}; `(4, 5)` would join nothing (there is no `foo(4)`).
    prog.input = vec![(2, 5)].into_iter().collect();
    prog.run();

    assert_eq!(prog.output.len(), 2);
    assert_eq!(prog.input.len(), 0);
}
