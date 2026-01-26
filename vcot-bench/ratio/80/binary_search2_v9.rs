use vstd::prelude::*;
fn main() {}

verus!{

// Complete the lemma function below
proof fn lemma_u64_div2_nonneg(x: int)
   

// Complete the lemma function below
proof fn lemma_u64_div2_le(x: int)
   

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

            assert(exists|i: int| i1 <= i <= i2 && k == v[i]) by {
                let w = choose|i: int| old_i1 <= i <= old_i2 && k == v[i];
                assert(old_i1 <= w && w <= old_i2 && k == v[w]);

                if w <= ix as int {
                    assert(0 <= w <= (ix as int) < v.len()) by {
                        assert(ix < v.len());
                    }
                    assert(v[w] <= v[ix as int]) by {
                        assert(forall|a:int, b:int| 0 <= a <= b < v.len() ==> v[a] <= v[b]);
                        assert(0 <= w <= (ix as int) < v.len());
                        assert(v[w] <= v[ix as int]);
                    }
                    assert(k <= v[ix as int]) by {
                        assert(k == v[w]);
                    }
                    assert(false) by { }
                }

                assert(i1 as int <= w) by {
                    assert(i1 == ix + 1);
                    assert(ix as int + 1 <= w);
                }
                assert(w <= i2 as int) by {
                    assert(i2 == old_i2);
                    assert(w <= old_i2);
                }
                assert(k == v[w]) by { }
                assert(exists|i:int| i1 <= i <= i2 && k == v[i]) by {
                    assert(i1 as int <= w <= i2 as int && k == v[w]);
                }
            }
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