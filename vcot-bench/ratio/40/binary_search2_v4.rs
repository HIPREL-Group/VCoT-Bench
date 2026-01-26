use vstd::prelude::*;
fn main() {}

verus!{

// Complete the lemma function below
proof fn lemma_u64_div2_nonneg(x: int)
   

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

// Complete the lemma function below
proof fn lemma_midpoint_bounds(i1: usize, i2: usize) -> (ix: usize)
   

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

    assert(i2 < v.len()) by {
        assert(v.len() > 0) by {
            let w = choose|i:int| 0 <= i < v.len() && k == v[i];
            assert(v.len() != 0) by { }
        }
        assert(v.len() - 1 < v.len()) by { }
    }

    while i1 != i2
        invariant
            i2 < v.len(),
            exists|i: int| i1 <= i <= i2 && k == v[i],
            forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
    {
        assert(i1 <= i2) by {
            let witness = choose|i: int| i1 <= i <= i2 && k == v[i];
            assert(i1 <= witness);
            assert(witness <= i2);
        }

        let ix = i1 + (i2 - i1) / 2;

        proof {
            let _ = lemma_midpoint_bounds(i1, i2);
        }

        assert(ix < v.len()) by {
            assert(ix <= i2);
            assert(i2 < v.len());
        }

        if v[ix] < k {
            let old_i1 = i1;
            let old_i2 = i2;

            i1 = ix + 1;

            // Fill in a block of assertions here to complete the proof
        } else {
            let old_i1 = i1;
            let old_i2 = i2;

            i2 = ix;

            assert(i2 < v.len()) by {
                assert(ix < v.len());
            }

            assert(exists|i: int| i1 <= i <= i2 && k == v[i]) by {
                let w = choose|i: int| old_i1 <= i <= old_i2 && k == v[i];
                assert(old_i1 <= w && w <= old_i2 && k == v[w]);

                if w > ix as int {
                    assert(w < v.len()) by {
                        assert(w <= old_i2);
                        assert(old_i2 < v.len());
                    }
                    assert(v[ix as int] <= v[w]) by {
                        assert(forall|a:int, b:int| 0 <= a <= b < v.len() ==> v[a] <= v[b]);
                        assert(0 <= (ix as int) <= w < v.len());
                        assert(v[ix as int] <= v[w]);
                    }
                    assert(v[ix as int] <= k) by {
                        assert(k == v[w]);
                    }
                    if v[ix as int] == k {
                        assert(i1 as int <= ix as int) by { assert(ix >= i1); }
                        assert(ix as int <= i2 as int) by { assert(i2 == ix); }
                        assert(exists|i:int| i1 <= i <= i2 && k == v[i]) by {
                            assert(i1 as int <= ix as int && ix as int <= i2 as int && k == v[ix as int]);
                        }
                    } else {
                        assert(v[ix as int] > k) by { }
                        assert(false) by { }
                    }
                } else {

                    assert(i1 as int <= w) by {
                        assert(i1 == old_i1);
                        assert(old_i1 <= w);
                    }
                    assert(w <= i2 as int) by {
                        assert(i2 == ix);
                        assert(w <= ix as int);
                    }
                    assert(k == v[w]) by { }
                    assert(exists|i:int| i1 <= i <= i2 && k == v[i]) by {
                        assert(i1 as int <= w <= i2 as int && k == v[w]);
                    }
                }
            }
        }
    }

    // Fill in a block of assertions here to complete the proof

    i1
}
}