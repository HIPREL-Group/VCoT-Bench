use vstd::prelude::*;

fn main() {}
verus! {

// Complete the lemma function below
proof fn lemma_mid_within_bounds(i1: usize, i2: usize)
   

// Complete the lemma function below
proof fn lemma_mid_progress(i1: usize, i2: usize)
   

// Complete the lemma function below
proof fn lemma_sorted_lt_implies_index_lt(
    v: &Vec<u64>,
    i: int,
    j: int,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i: int| 0 <= i < v.len() && k == v[i],
    ensures
        r < v.len(),
        k == v[r as int],
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;

    while i1 != i2
        // Fill in loop invariants here
    {
        let ghost d = i2 - i1;

        // Fill in a block of assertions here to complete the proof;

        let ix = i1 + (i2 - i1) / 2;

        // Fill in a block of assertions here to complete the proof

        if v[ix] < k {
            // Fill in a block of assertions here to complete the proof
            i1 = ix + 1;
        } else {
            // Fill in a block of assertions here to complete the proof
            i2 = ix;
        }

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof

    i1
}

} // verus!