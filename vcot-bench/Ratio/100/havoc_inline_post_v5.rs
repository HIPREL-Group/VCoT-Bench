use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::exec_allows_no_decreases_clause]
pub fn havoc_inline_post(v: &mut Vec<u32>, a: u32, b: bool)
    requires 
        forall |k:int| 0 <= k < old(v).len() ==> old(v)[k] > 0,
        a > 0,
        b == false,
{  
    assume(10 < a < 20);
    assume(forall |k:int| 0 <= k < v.len() ==> v[k] == 1);

    let c: bool = !b;

    let mut idx: usize = v.len();

    // Fill in a block of assertions here to complete the proof

    while (idx > 0)
        // Fill in loop invariants here
    {
        let old_idx = idx;
        idx = idx - 1;

        let temp = v[idx];

        // Fill in a block of assertions here to complete the proof

        v.set(idx, temp + a);

        // Fill in a block of assertions here to complete the proof
    }
    
    // Fill in a block of assertions here to complete the proof
}
}