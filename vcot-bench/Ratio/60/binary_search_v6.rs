use vstd::prelude::*;

fn main() {}
verus! {

proof fn lemma_mid_within_bounds(i1: usize, i2: usize)
    requires
        i1 <= i2,
    ensures
        i1 <= i1 + (i2 - i1) / 2,
        i1 + (i2 - i1) / 2 <= i2,
{
    let d: int = i2 - i1;

    assert(d / 2 <= d);

    assert(i1 <= i1 + d / 2);
    assert(i1 + d / 2 <= i1 + d);

    assert(i1 + d == i2);
}

proof fn lemma_mid_progress(i1: usize, i2: usize)
    requires
        i1 < i2,
    ensures
        i1 + (i2 - i1) / 2 < i2,
{
    let d: int = i2 - i1;
    assert(d > 0);

    assert(d / 2 < d);

    assert(i1 + d / 2 < i1 + d);

    assert(i1 + d == i2);
}

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
        invariant
            i2 < v.len(),
            exists|i: int| i1 <= i <= i2 && k == v[i],
            forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
    {
        let ghost d = i2 - i1;

        // Fill in a block of assertions here to complete the proof;

        let ix = i1 + (i2 - i1) / 2;

        proof {
            lemma_mid_within_bounds(i1, i2);
            lemma_mid_progress(i1, i2);

            assert(i1 <= ix);
            assert(ix <= i2);
            assert(ix < i2);

            assert(i1 <= ix && ix <= i2);
            assert(ix < i2);

            assert(ix < v.len()) by {
                assert(i2 < v.len());
                assert(ix <= i2);
            }
        }

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