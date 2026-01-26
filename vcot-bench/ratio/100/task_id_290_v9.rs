use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_exists_preserved_if_max_unchanged(
    seq: &Vec<Vec<i32>>,
    old_max: &Vec<i32>,
    new_max: &Vec<i32>,
    index: int,
)
   

// Complete the lemma function below
proof fn lemma_forall_extend_by_one_using_compare(
    seq: &Vec<Vec<i32>>,
    old_max: &Vec<i32>,
    new_max: &Vec<i32>,
    index: int,
)
   

// Complete the lemma function below
proof fn lemma_exists_extend_by_one_with_new_index(
    seq: &Vec<Vec<i32>>,
    new_max: &Vec<i32>,
    index: int,
)
   

// Complete the lemma function below
proof fn lemma_forall_extend_by_one_when_update(
    seq: &Vec<Vec<i32>>,
    old_max: &Vec<i32>,
    new_max: &Vec<i32>,
    index: int,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn max_length_list(seq: &Vec<Vec<i32>>) -> (max_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && max_list@ =~= #[trigger] (seq[k]@),
{
    let mut max_list = &seq[0];
    // Fill in a block of assertions here to complete the proof;
    let mut index = 1;

    while index < seq.len()
        // Fill in loop invariants here
    {
        if ((seq[index]).len() > max_list.len()) {
            let old_max = max_list;
            max_list = &seq[index];

            // Fill in a block of assertions here to complete the proof
        } else {
            let old_max = max_list;
            // Fill in a block of assertions here to complete the proof
        }

        index += 1;
    }

    // Fill in a block of assertions here to complete the proof;

    max_list
}

} // verus!