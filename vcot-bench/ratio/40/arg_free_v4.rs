use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_gap_preserved_by_inc(gap: u64, res: u64, idx: u64)
    requires
        gap == res - idx,
        idx + 1 <= res + 1,
    ensures
        gap == (res + 1) - (idx + 1),
{
    assert((res + 1) - (idx + 1) == res - idx);
}

#[verifier::exec_allows_no_decreases_clause]
fn choose_odd()
{
    let mut idx: u64 = 0;
    let mut res: u64 = 5;

    let ghost gap = res-idx;

    assert(gap < 100) by {
        assert(res == 5);
        assert(idx == 0);
        assert(gap == 5);
        assert(5 < 100);
    }

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

    assert(gap < 100) by {
        assert(res == 15);
        assert(idx == 0);
        assert(gap == 15);
        assert(15 < 100);
    }

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