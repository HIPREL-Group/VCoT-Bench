use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_prefix_extend_with_new_not_target(arr: &Vec<i32>, target: i32, i: int)
    requires
        0 <= i,
        i < arr.len(),
        forall|k: int| 0 <= k < i ==> arr[k] != target,
        arr[i as int] != target,
    ensures
        forall|k: int| 0 <= k < i + 1 ==> arr[k] != target,
{
    assert(forall|k: int| 0 <= k < i + 1 ==> arr[k] != target) by {
        assert forall|k: int| 0 <= k < i + 1 implies arr[k] != target by {
            if k < i {
                assert(0 <= k < i);
                assert(arr[k] != target);
            } else {
                assert(k == i);
                assert(arr[i as int] != target);
            }
        }
    }
}

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