use vstd::prelude::*;
fn main() {}
verus! {

proof fn lemma_forall_extend_max(x: &Vec<i32>, max_index: usize, i: usize)
    requires
        i < x.len(),
        max_index < x.len(),
        forall|k: int| 0 <= k < i ==> x[max_index as int] >= x[k],
        x[i as int] > x[max_index as int],
    ensures
        forall|k: int| 0 <= k < (i + 1) ==> x[i as int] >= x[k],
{
    assert(forall|k: int| 0 <= k < (i + 1) ==> x[i as int] >= x[k]) by {
        assert forall|k: int| 0 <= k < (i + 1) implies x[i as int] >= x[k] by {
            let k = k;
            if k == i as int {
            } else {
                assert(x[max_index as int] >= x[k]);
            }
        };
    };
}

proof fn lemma_forall_extend_keep_max(x: &Vec<i32>, max_index: usize, i: usize)
    requires
        i < x.len(),
        max_index < x.len(),
        forall|k: int| 0 <= k < i ==> x[max_index as int] >= x[k],
        !(x[i as int] > x[max_index as int]),
    ensures
        forall|k: int| 0 <= k < (i + 1) ==> x[max_index as int] >= x[k],
{
    assert(forall|k: int| 0 <= k < (i + 1) ==> x[max_index as int] >= x[k]) by {
        assert forall|k: int| 0 <= k < (i + 1) implies x[max_index as int] >= x[k] by {
            let k = k;
            if k == i as int {
            } else {
                assert(x[max_index as int] >= x[k]);
            }
        };
    };
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun1(x: &Vec<i32>) -> (max_index: usize)
    requires
        x.len() >= 1,
    ensures
        forall|k: int| 0 <= k < x.len() ==> x[max_index as int] >= x[k],
        max_index < x.len(),
{
    let mut max_index = 0;
    let mut i: usize = 1;

    assert(forall|k: int| 0 <= k < i ==> x[max_index as int] >= x[k]) by {
        assert forall|k: int| 0 <= k < i implies x[max_index as int] >= x[k] by {
            let k = k;
            assert(x[max_index as int] >= x[k]) by {
                assert(max_index as int == k);
                assert(x[max_index as int] == x[k]);
            };
        };
    };

    while (i < x.len())
        invariant
            i <= x.len(),
            max_index < x.len(),
            forall|k: int| 0 <= k < i ==> x[max_index as int] >= x[k],
    {
        if x[i] > x[max_index] {
            proof {
                lemma_forall_extend_max(x, max_index, i);
            }
            max_index = i;
            assert(forall|k: int| 0 <= k < (i + 1) ==> x[max_index as int] >= x[k]);
        } else {
            proof {
                lemma_forall_extend_keep_max(x, max_index, i);
            }
            assert(forall|k: int| 0 <= k < (i + 1) ==> x[max_index as int] >= x[k]);
        }

        i = i + 1;
    }

    max_index
}

} // verus!