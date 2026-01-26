use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_forall_extend(arr1: &Vec<i32>, arr2: &Vec<i32>, i: int)
    requires
        arr1.len() == arr2.len(),
        0 <= i < arr1.len(),
        forall|k: int| 0 <= k < i ==> arr1[k] > arr2[k],
        arr1[i] > arr2[i],
    ensures
        forall|k: int| 0 <= k < i + 1 ==> arr1[k] > arr2[k],
{
    assert(forall|k: int| 0 <= k < i + 1 ==> arr1[k] > arr2[k]) by {
        assert forall|k: int| 0 <= k < i + 1 implies arr1[k] > arr2[k] by {
            if k < i {
                assert(arr1[k] > arr2[k]);
            } else {
                assert(k == i) by {
                    assert(k < i + 1);
                    assert(!(k < i));
                    assert(k >= i);
                };
                assert(arr1[k] > arr2[k]);
            }
        };
    };
}

proof fn lemma_exists_counterexample_from_prefix_violation(
    arr1: &Vec<i32>,
    arr2: &Vec<i32>,
    index: int,
)
    requires
        arr1.len() == arr2.len(),
        0 <= index < arr1.len(),
        !(arr1[index] > arr2[index]),
    ensures
        !(forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
{
    assert(!(forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i])) by {
        let i = index;
        assert(!(arr1[i] > arr2[i]));
    };
}

proof fn lemma_forall_from_prefix_at_end(arr1: &Vec<i32>, arr2: &Vec<i32>, index: int)
    requires
        arr1.len() == arr2.len(),
        index == arr1.len(),
        forall|k: int| 0 <= k < index ==> arr1[k] > arr2[k],
    ensures
        forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i],
{
    assert(forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]) by {
        assert forall|i: int| 0 <= i < arr1.len() implies arr1[i] > arr2[i] by {
            assert(i < index) by {
                assert(index == arr1.len());
            };
            assert(arr1[i] > arr2[i]);
        };
    };
}

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
    // Fill in a block of assertions here to complete the proof;
    true
}

} // verus!