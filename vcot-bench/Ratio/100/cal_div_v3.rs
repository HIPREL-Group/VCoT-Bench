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
        // Fill in loop invariants here
    {
        x = x + 1;
        y = 191 - 7 * x;
    }
    // Fill in a block of assertions here to complete the proof

    (x, y)
}

} // verus!
fn main() {}