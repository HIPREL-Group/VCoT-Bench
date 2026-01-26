use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_extend_outer_invariant_on_i_increment(i: int, list1: &Vec<i32>, list2: &Vec<i32>)
   

// Complete the lemma function below
proof fn lemma_inner_invariant_preserved_after_j_increment(
    i: int,
    j_old: int,
    list1: &Vec<i32>,
    list2: &Vec<i32>,
)
   

// Complete the lemma function below
proof fn lemma_no_common_element_from_forall_neq(
    list1: &Vec<i32>,
    list2: &Vec<i32>,
    i_end: int,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
{
    let mut i = 0;
    while i < list1.len()
        // Fill in loop invariants here
    {
        let mut j = 0;
        while j < list2.len()
            invariant
                0 <= i < list1.len(),
                0 <= j <= list2.len(),
                forall|k: int| 0 <= k < j ==> (list1[i as int] != list2[k]),
        {
            if list1[i] == list2[j] {
                assert(exists|ii: int, jj: int|
                    0 <= ii < list1.len() && 0 <= jj < list2.len() && (list1[ii] == list2[jj])) by {
                    assert(list1[i as int] == list2[j as int]);
                };
                return true;
            }

            let j_old = j;
            j += 1;

            // Fill in a block of assertions here to complete the proof
        }

        // Fill in a block of assertions here to complete the proof

        i += 1;
    }

    // Fill in a block of assertions here to complete the proof;

    false
}

} // verus!