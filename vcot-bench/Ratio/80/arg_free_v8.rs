use vstd::prelude::*;
fn main() {}

verus!{

// Complete the lemma function below
proof fn lemma_gap_preserved_by_inc(gap: u64, res: u64, idx: u64)
   

#[verifier::exec_allows_no_decreases_clause]
fn choose_odd()
{
    let mut idx: u64 = 0;
    let mut res: u64 = 5;

    let ghost gap = res-idx;

    // Fill in a block of assertions here to complete the proof

    while (idx < 10)
    // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof

        let ghost idx_old = idx;
        let ghost res_old = res;

        res = res + 1;
        idx = idx + 1;

        // Fill in a block of assertions here to complete the proof
    }
    idx = 0;

    let ghost gap = res - idx;

    // Fill in a block of assertions here to complete the proof

    while (idx < 10)
    // Fill in loop invariants here
    {

        // Fill in a block of assertions here to complete the proof

        let ghost idx_old = idx;
        let ghost res_old = res;

        res = res + 1;
        idx = idx + 1;

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof;
}
}