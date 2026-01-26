use vstd::prelude::*;
fn main() {}
verus! {

// Complete the lemma function below
proof fn lemma_forall_extend_max(x: &Vec<i32>, max_index: usize, i: usize)
   

proof fn lemma_forall_extend_keep_max(x: &Vec<i32>, max_index: usize, i: usize)
    requires
        i < x.len(),
        max_index < x.len(),
        forall|k: int| 0 <= k < i ==> x[max_index as int] >= x[k],
        !(x[i as int] > x[max_index as int]),
    ensures
        forall|k: int| 0 <= k < (i + 1) ==> x[max_index as int] >= x[k],
{
    // Fill in a block of assertions here to complete the proof by {
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

    // Fill in a block of assertions here to complete the proof;

    while (i < x.len())
        // Fill in loop invariants here
    {
        if x[i] > x[max_index] {
            // Fill in a block of assertions here to complete the proof
            max_index = i;
            // Fill in a block of assertions here to complete the proof;
        } else {
            proof {
                lemma_forall_extend_keep_max(x, max_index, i);
            }
            // Fill in a block of assertions here to complete the proof;
        }

        i = i + 1;
    }

    max_index
}

} // verus!