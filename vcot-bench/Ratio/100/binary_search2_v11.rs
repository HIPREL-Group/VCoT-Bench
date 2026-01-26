use vstd::prelude::*;
fn main() {}

verus!{

// Complete the lemma function below
proof fn lemma_u64_div2_nonneg(x: int)
   

// Complete the lemma function below
proof fn lemma_u64_div2_le(x: int)
   

// Complete the lemma function below
proof fn lemma_midpoint_bounds(i1: usize, i2: usize) -> (ix: usize)
   

// Complete the lemma function below
proof fn lemma_midpoint_ix_in_bounds(i1: usize, i2: usize, ix: usize)
   

#[verifier::exec_allows_no_decreases_clause]
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i:int| 0 <= i < v.len() && k == v[i],
    ensures
        r < v.len(),
        k == v[r as int],
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;

    // Fill in a block of assertions here to complete the proof

    while i1 != i2
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof

        let ix = i1 + (i2 - i1) / 2;

        // Fill in a block of assertions here to complete the proof

        if v[ix] < k {
            let old_i1 = i1;
            let old_i2 = i2;

            i1 = ix + 1;

            // Fill in a block of assertions here to complete the proof
        } else {
            let old_i1 = i1;
            let old_i2 = i2;

            i2 = ix;

            // Fill in a block of assertions here to complete the proof
        }
    }

    // Fill in a block of assertions here to complete the proof

    i1
}
}