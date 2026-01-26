use vstd::prelude::*;

verus! {

// Complete the lemma function below
proof fn lemma_postcondition_from_inv_and_exit(x: u32, y: u32)
   

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
    assert(7u32 * x + y == 191u32);
    assert(!(7 <= y));

    proof {
        lemma_postcondition_from_inv_and_exit(x, y);
    }

    (x, y)
}

} // verus!
fn main() {}