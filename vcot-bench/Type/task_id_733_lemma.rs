use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_prefix_extend_with_new_not_target(arr: &Vec<i32>, target: i32, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (index: Option<usize>)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        if let Some(idx) = index {
            &&& 0 <= idx < arr.len()
            &&& forall|k: int| 0 <= k < idx ==> arr[k] != target
            &&& arr[idx as int] == target
        } else {
            forall|k: int| 0 <= k < arr.len() ==> arr[k] != target
        },
{
    let mut index = 0;

    while index < arr.len()
        invariant
            forall|k: int| 0 <= k < index ==> arr[k] != target,
    {
        if arr[index] == target {
            return Some(index);
        }

        proof {
            lemma_prefix_extend_with_new_not_target(arr, target, index as int);
        }

        index += 1;
    }

    None
}

} // verus!