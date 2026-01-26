use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_extend(arr1: &Vec<i32>, arr2: &Vec<i32>, i: int)
   

// Complete the lemma function below
proof fn lemma_exists_counterexample_from_prefix_violation(
    arr1: &Vec<i32>,
    arr2: &Vec<i32>,
    index: int,
)
   

// Complete the lemma function below
proof fn lemma_forall_from_prefix_at_end(arr1: &Vec<i32>, arr2: &Vec<i32>, index: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    requires
        arr1.len() == arr2.len(),
    ensures
        result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
{
    let mut index = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            arr1.len() == arr2.len(),
            forall|k: int| 0 <= k < index ==> arr1[k] > arr2[k],
    {
        if arr1[index] <= arr2[index] {
            assert(!(forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i])) by {
                lemma_exists_counterexample_from_prefix_violation(arr1, arr2, index as int);
            };
            return false;
        }
        assert(arr1[(index as int)] > arr2[(index as int)]);

        let old_index = index;
        index += 1;

        assert(forall|k: int| 0 <= k < index ==> arr1[k] > arr2[k]) by {
            lemma_forall_extend(arr1, arr2, old_index as int);
        };
    }
    assert(forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]) by {
        lemma_forall_from_prefix_at_end(arr1, arr2, index as int);
    };
    true
}

} // verus!