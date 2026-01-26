use vstd::prelude::*;

verus! {

proof fn lemma_postcondition_from_inv_and_exit(x: u32, y: u32)
    requires
        0u32 <= y,
        7u32 * x + y == 191u32,
        !(7u32 <= y),
    ensures
        x == 27u32,
        y == 2u32,
{
    assert(y < 7u32);

    assert(7u32 * x <= 191u32);

    assert(y == 191u32 - 7u32 * x);

    assert(191u32 - 7u32 * x < 7u32);

    assert(7u32 * x > 184u32);

    assert(7u32 * x >= 185u32);

    assert(7u32 * x == 189u32) by {
        assert(7u32 * x <= 191u32);
        assert(7u32 * x >= 185u32);
        assert((7u32 * x) as int % 7 == 0);
        assert((185u32 as int) % 7 == 3);
        assert((186u32 as int) % 7 == 4);
        assert((187u32 as int) % 7 == 5);
        assert((188u32 as int) % 7 == 6);
        assert((189u32 as int) % 7 == 0);
        assert((190u32 as int) % 7 == 1);
        assert((191u32 as int) % 7 == 2);
    }

    assert(x == 27u32) by {
        assert(7u32 * x == 189u32);
        assert(7u32 * 27u32 == 189u32);
    }

    assert(y == 2u32) by {
        assert(7u32 * x + y == 191u32);
        assert(x == 27u32);
        assert(7u32 * x == 189u32);
        assert(189u32 + y == 191u32);
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn cal_div() -> (r: (u32, u32))
    ensures
        r.0 == 27,
        r.1 == 2,
{
    let mut x: u32 = 0;
    let mut y: u32 = 191;
    while 7 <= y
        invariant
            0 <= y,
            7u32 * x + y == 191u32,
    {
        x = x + 1;
        y = 191 - 7 * x;
    }
    // Fill in a block of assertions here to complete the proof

    (x, y)
}

} // verus!
fn main() {}