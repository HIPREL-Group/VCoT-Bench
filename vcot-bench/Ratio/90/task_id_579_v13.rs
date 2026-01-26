use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
   

#[verifier::exec_allows_no_decreases_clause]
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;

    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] == key) {
            assert(exists|i: int| 0 <= i < arr.len() && arr[i] == key) by {
                assert(arr[index as int] == key);
            };
            return true;
        }

        // Fill in a block of assertions here to complete the proof;

        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }

    // Fill in a block of assertions here to complete the proof;

    false
}

// Complete the lemma function below
proof fn lemma_seq_contains_witness<T>(s: Seq<T>, x: T, i: int)
   

// Complete the lemma function below
proof fn lemma_seq_not_contains_implies_index_ne<T>(s: Seq<T>, x: T, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
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

            // Fill in a block of assertions here to complete the proof
        }
        index += 1;
    }
    let mut index = 0;
    while index < arr2.len()
        // Fill in loop invariants here
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            // Fill in a block of assertions here to complete the proof
            result.push(arr2[index]);

            proof {
                let pushed = arr2[index as int];
                assert(result@.contains(pushed)) by {
                    let new_len: int = (result@.len() as int);
                    assert(result@.index(new_len - 1) == pushed) by {
                        assert(result@.index((result.len() - 1) as int) == pushed);
                    };
                    lemma_seq_contains_witness(result@, pushed, new_len - 1);
                };
                assert(forall|m: int, n: int|
                    0 <= m < n < result.len() ==> #[trigger] result[m] != #[trigger] result[n]
                );
            }
        }
        index += 1;
    }
    // Fill in a block of assertions here to complete the proof;

    result
}

} // verus!