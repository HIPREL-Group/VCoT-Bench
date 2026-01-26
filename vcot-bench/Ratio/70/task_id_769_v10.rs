use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    assert(forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k]) by {
        assert forall|k: int| 0 <= k < vec.len() implies #[trigger] vec[k] == vec.push(i)[k] by {
            assert(vec.push(i)[k] == vec[k]) by {
                assert(vec.push(i).index(k) == vec.index(k));
            }
        }
    }
}

proof fn lemma_contains_contrapositive(arr: &Vec<i32>, key: i32, index: int)
    requires
        0 <= index <= arr.len(),
        forall|m: int| 0 <= m < index ==> arr[m] != key,
    ensures
        !exists|i: int| 0 <= i < index && arr[i] == key,
{
    assert(!exists|i: int| 0 <= i < index && arr[i] == key) by {
        if exists|i: int| 0 <= i < index && arr[i] == key {
            let i = choose|i: int| 0 <= i < index && arr[i] == key;

            assert(arr[i] != key) by {
                assert(forall|m: int| 0 <= m < index ==> arr[m] != key);
            }
            assert(false);
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;

    assert(forall|m: int| 0 <= m < index ==> (arr[m] != key)) by {
        assert forall|m: int| 0 <= m < index implies (arr[m] != key) by {
            assert(false);
        }
    }

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|m: int| 0 <= m < index ==> (arr[m] != key),
    {
        if (arr[index] == key) {
            // Fill in a block of assertions here to complete the proof
            return true;
        }

        // Fill in a block of assertions here to complete the proof;

        let old_index = index;
        index += 1;

        assert(forall|m: int| 0 <= m < index ==> (arr[m] != key)) by {
            assert forall|m: int| 0 <= m < index implies (arr[m] != key) by {
                if m < old_index as int {
                    assert(forall|m2: int| 0 <= m2 < old_index as int ==> (arr[m2] != key));
                } else {
                    assert(arr[m] != key);
                }
            }
        }
    }

    // Fill in a block of assertions here to complete the proof

    false
}

// Complete the lemma function below
proof fn lemma_distinct_after_push<T>(s: Seq<T>, x: T)
   

// Complete the lemma function below
proof fn lemma_distinct_pairwise_after_push_i32(s: Seq<i32>, x: i32)
   

#[verifier::exec_allows_no_decreases_clause]
fn difference(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
{
    let mut result = Vec::new();
    let ghost mut output_len: int = 0;

    let mut index = 0;

    while index < arr1.len()
        // Fill in loop invariants here
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            // Fill in a block of assertions here to complete the proof
            result.push(arr1[index]);
        }
        index += 1;
    }

    index = 0;

    while index < arr2.len()
        // Fill in loop invariants here
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            // Fill in a block of assertions here to complete the proof
            result.push(arr2[index]);
        }
        index += 1;
    }

    // Fill in a block of assertions here to complete the proof

    result
}

} // verus!