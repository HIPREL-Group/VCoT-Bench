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

proof fn lemma_sorted_lt_implies_index_lt(
    v: &Vec<u64>,
    i: int,
    j: int,
)
    requires
        forall|i2: int, j2: int| 0 <= i2 <= j2 < v.len() ==> v[i2] <= v[j2],
        0 <= i <= j < v.len(),
        v[i] < v[j],
    ensures
        i < j,
{
    if i == j {
        assert(v[i] <= v[j]) by {
            assert(0 <= i <= j < v.len());
        }
        assert(false);
    } else {
        assert(i < j);
    }
}

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

        assert(i1 < i2);

        let ix = i1 + (i2 - i1) / 2;

        // Fill in a block of assertions here to complete the proof

        if v[ix] < k {
            // Fill in a block of assertions here to complete the proof
            i1 = ix + 1;
        } else {
            // Fill in a block of assertions here to complete the proof
            i2 = ix;
        }

        proof {
            assert(i2 - i1 < d);
        }
    }

    proof {
        assert(i1 < v.len()) by {
            assert(i2 < v.len());
        }
        let ghost w = choose|t: int| i1 <= t <= i2 && k == v[t];
        assert(k == v[(i1 as int)]) by {
            assert(k == v[w]);
            assert(w == (i1 as int));
        }
    }

    i1
}

} // verus!