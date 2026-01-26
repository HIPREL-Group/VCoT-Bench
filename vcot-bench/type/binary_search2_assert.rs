use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_u64_div2_nonneg(x: int)
    requires
        0 <= x,
    ensures
        0 <= x / 2,
{
    assert(0 <= x / 2) by {
        let q: int = x / 2;
        let r: int = x % 2;
        assert(x == 2 * q + r) by {
            assert(x == 2 * (x / 2) + (x % 2)) by (compute);
        }
        assert(0 <= r) by {
            assert(0 <= x % 2) by (compute);
        }
        assert(r < 2) by {
            assert(x % 2 < 2) by (compute);
        }
        if q < 0 {
            assert(2 * q <= -2) by {
            }
            assert(r <= 1) by {
            }
            assert(2 * q + r <= -1) by {
            }
            assert(x < 0) by {
                assert(x == 2 * q + r);
            }
            assert(false) by {
                assert(0 <= x);
            }
        }
    }
}

proof fn lemma_u64_div2_le(x: int)
    requires
        0 <= x,
    ensures
        x / 2 <= x,
{
    assert(2 > 0) by (compute);

    let q: int = x / 2;
    let r: int = x % 2;
    assert(x == 2 * q + r) by {
        assert(x == 2 * (x / 2) + (x % 2)) by (compute);
    }
    assert(0 <= r) by { assert(0 <= x % 2) by (compute); }
    assert(r < 2) by { assert(x % 2 < 2) by (compute); }

    if q <= x {
        assert(x / 2 <= x);
    } else {
        assert(2 * q + r >= 2 * (x + 1) + 0) by {
            assert(0 <= r);
        }
        assert(2 * (x + 1) + 0 == 2 * x + 2) by (compute);
        assert(x == 2 * q + r);
        assert(false) by {
        }
    }
}

proof fn lemma_midpoint_bounds(i1: usize, i2: usize) -> (ix: usize)
    requires
        i1 <= i2,
    ensures
        ix == i1 + (i2 - i1) / 2,
        ix >= i1,
        ix <= i2,
{
    let d: int = i2 as int - i1 as int;
    let ix0: int = i1 as int + d / 2;
    assert(ix0 == i1 as int + (i2 as int - i1 as int) / 2) by { }
    assert(ix0 >= i1 as int) by { }
    assert(ix0 <= i2 as int) by {
        assert(d / 2 <= d) by {
            lemma_u64_div2_le(d);
            assert(d / 2 <= d);
        }
        assert(i1 as int + d / 2 <= i1 as int + d) by { }
        assert(i1 as int + d == i2 as int) by { }
    }
    ix0 as usize
}

proof fn lemma_midpoint_ix_in_bounds(i1: usize, i2: usize, ix: usize)
    requires
        i1 <= i2,
        ix == i1 + (i2 - i1) / 2,
    ensures
        ix >= i1,
        ix <= i2,
{
    let _ = lemma_midpoint_bounds(i1, i2);
    assert(ix >= i1) by {
        assert(ix == i1 + (i2 - i1) / 2);
    }
    assert(ix <= i2) by {
        assert(ix == i1 + (i2 - i1) / 2);
        assert((i2 - i1) / 2 <= (i2 - i1)) by {
            let di: int = (i2 - i1) as int;
            lemma_u64_div2_le(di);
            assert(((i2 - i1) / 2) as int <= (i2 - i1) as int);
        }
        assert(i1 + (i2 - i1) / 2 <= i1 + (i2 - i1)) by { }
        assert(i1 + (i2 - i1) == i2) by { }
    }
}

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
        invariant
            i2 < v.len(),
            exists|i: int| i1 <= i <= i2 && k == v[i],
            forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
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