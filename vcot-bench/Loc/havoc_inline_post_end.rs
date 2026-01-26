use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::exec_allows_no_decreases_clause]
pub fn havoc_inline_post(v: &mut Vec<u32>, a: u32, b: bool)
    requires 
        forall |k:int| 0 <= k < old(v).len() ==> old(v)[k] > 0,
        a > 0,
        b == false,
{  
    assume(10 < a < 20);
    assume(forall |k:int| 0 <= k < v.len() ==> v[k] == 1);

    let c: bool = !b;

    let mut idx: usize = v.len();

    assert(forall |k:int| (idx as int) <= k < v.len() ==> v[k] == 1 + a) by {
        assert forall |k:int| (idx as int) <= k < v.len() implies v[k] == 1 + a by {
            assert(false) by {
                assert((idx as int) == v.len());
                assert((idx as int) <= k < v.len());
            }
        }
    }
    assert(forall |k:int| 0 <= k < (idx as int) ==> v[k] == 1) by {
        assert forall |k:int| 0 <= k < (idx as int) implies v[k] == 1 by {
            assert(0 <= k < v.len());
        }
    }

    while (idx > 0)
        invariant
            0 <= (idx as int) <= v.len(),
            forall |k:int| (idx as int) <= k < v.len() ==> v[k] == 1 + a,
            forall |k:int| 0 <= k < (idx as int) ==> v[k] == 1,
            10 < a < 20,
    {
        let old_idx = idx;
        idx = idx - 1;

        let temp = v[idx];

        assert(temp == 1u32) by {
            assert(0 <= (idx as int) < (old_idx as int));
        }

        v.set(idx, temp + a);

        assert(v[(idx as int)] == 1u32 + a) by {
            assert(temp == 1u32);
        }

        assert(forall |k:int| (idx as int) <= k < v.len() ==> v[k] == 1 + a) by {
            assert forall |k:int| (idx as int) <= k < v.len() implies v[k] == 1 + a by {
                if k == (idx as int) {
                    assert(v[k] == v[(idx as int)]);
                } else {
                    assert(v[k] == 1 + a);
                }
            }
        }

        assert(forall |k:int| 0 <= k < (idx as int) ==> v[k] == 1) by {
            assert forall |k:int| 0 <= k < (idx as int) implies v[k] == 1 by {
                assert(v[k] == 1) by {
                    assert(0 <= k < (old_idx as int));
                }
            }
        }
    }
    
    // Fill in a block of assertions here to complete the proof
}
}