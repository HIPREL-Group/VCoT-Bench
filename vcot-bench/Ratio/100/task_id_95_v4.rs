use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_min_update_preserves_forall(
    list: &Vec<Vec<i32>>,
    index: usize,
    old_min: usize,
    new_min: usize,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)
    requires
        list.len() > 0,
    ensures
        min >= 0,
        forall|i: int| 0 <= i < list.len() ==> min <= #[trigger] list[i].len(),
        exists|i: int| 0 <= i < list.len() && min == #[trigger] list[i].len(),
{
    let mut min = list[0].len();

    let mut index = 1;
    while index < list.len()
        // Fill in loop invariants here
    {
        if (&list[index]).len() < min {
            let old_min = min;
            let new_min = (&list[index]).len();

            min = new_min;

            // Fill in a block of assertions here to complete the proof
        } else {
            // Fill in a block of assertions here to complete the proof
        }
        index += 1;
    }
    min
}

}