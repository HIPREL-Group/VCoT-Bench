use vstd::prelude::*;

fn main() {}
verus! {

// Complete the lemma function below
proof fn lemma_mid_within_bounds(i1: usize, i2: usize)
   

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
        // Fill in loop invariants here
    {
        let ghost d = i2 - i1;

        assert(i1 < i2);

        let ix = i1 + (i2 - i1) / 2;

        // Fill in a block of assertions here to complete the proof

        if v[ix] < k {
            proof {
                let ghost w = choose|t: int| i1 <= t <= i2 && k == v[t];

                assert(k == v[w]);

                assert(v[(ix as int)] < v[w]) by {
                    assert(k == v[w]);
                }

                assert((ix as int) < w) by {
                    lemma_sorted_lt_implies_index_lt(v, (ix as int), w);
                }

                assert(ix + 1 <= (w as usize)) by {
                    assert((ix as int) + 1 <= w);
                }
                assert(ix + 1 <= i2) by {
                    assert(ix < i2);
                }

                assert(exists|t: int| (ix + 1) <= t <= i2 && k == v[t]) by {
                    assert(((ix + 1) as int) <= w);
                }
            }
            i1 = ix + 1;
        } else {
            proof {
                let ghost w = choose|t: int| i1 <= t <= i2 && k == v[t];

                assert(k == v[w]);

                assert(k <= v[(ix as int)]) by {
                    assert(!(v[(ix as int)] < k));
                }
                
                if w <= (ix as int) {
                     assert(exists|t: int| i1 <= t <= ix && k == v[t]);
                } else {
                     assert((ix as int) < w);
                     assert(v[(ix as int)] <= v[w]);
                     assert(v[w] == k);
                     assert(v[(ix as int)] == k);
                     assert(exists|t: int| i1 <= t <= ix && k == v[t]);
                }
            }
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