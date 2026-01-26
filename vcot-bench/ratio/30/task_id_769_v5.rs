use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
   

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
            assert(exists|i: int| 0 <= i < arr.len() && arr[i] == key) by {
                let i: int = index as int;
                assert(arr[i] == key);
            }
            return true;
        }

        assert(arr[(index as int)] != key);

        let old_index = index;
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }

    proof {
        lemma_contains_contrapositive(arr, key, index as int);
    }

    false
}

// Complete the lemma function below
proof fn lemma_distinct_after_push<T>(s: Seq<T>, x: T)
   

proof fn lemma_distinct_pairwise_after_push_i32(s: Seq<i32>, x: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i] != #[trigger] s[j],
        !s.contains(x),
    ensures
        forall|i: int, j: int|
            0 <= i < j < s.push(x).len() ==> #[trigger] s.push(x)[i] != #[trigger] s.push(x)[j],
{
    lemma_distinct_after_push(s, x);
}

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
        invariant
            0 <= index <= arr1.len(),
            forall|i: int|
                0 <= i < index ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                    arr1[i],
                )),
            forall|m: int, n: int|
                0 <= m < n < result.len() ==> #[trigger] result[m] != #[trigger] result[n],
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
            proof {
                lemma_vec_push(result@, arr2[index as int], result.len());

                assert(!result@.contains(arr2[index as int]));
                lemma_distinct_after_push(result@, arr2[index as int]);

                output_len = output_len + 1;

                assert(forall|m: int, n: int|
                    0 <= m < n < result@.push(arr2[index as int]).len()
                    ==> #[trigger] result@.push(arr2[index as int])[m]
                        != #[trigger] result@.push(arr2[index as int])[n]) by {
                    lemma_distinct_pairwise_after_push_i32(result@, arr2[index as int]);
                }
            }
            result.push(arr2[index]);
        }
        index += 1;
    }

    proof {
        assert(result@.len() == result.len() as int);
        assert(arr1@.len() == arr1.len() as int);
        assert(arr2@.len() == arr2.len() as int);
    }

    result
}

} // verus!