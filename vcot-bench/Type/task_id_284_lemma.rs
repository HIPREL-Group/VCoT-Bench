use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_prefix_extend_i32(arr: &Vec<i32>, element: i32, n: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
{
    let mut index = 0;

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|k: int| 0 <= k < index ==> (arr[k] == element),
    {
        if arr[index] != element {
            proof {
                let i = (index as int);

                assert(!(forall|j: int| 0 <= j < arr.len() ==> arr[j] == element)) by {
                    assert(exists|j: int| 0 <= j < arr.len() && arr[j] != element) by {
                        assert(arr[i] != element);
                    }
                }
            }

            return false;
        }

        let old_index = index;
        index += 1;

        assert(forall|k: int| 0 <= k < index ==> (arr[k] == element)) by {
            let n: int = (old_index as int);

            assert(arr[n] == element) by {
                assert(arr[(old_index as int)] == element);
            };

            lemma_forall_prefix_extend_i32(arr, element, n);

            assert(n + 1 == (index as int)) by {
                assert(index == old_index + 1);
            };
        };
    }

    assert(forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)) by {
        assert(forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)) by {
            assert forall|i: int| 0 <= i < arr.len() implies arr[i] == element by {
                assert(0 <= i < index);
                assert(arr[i] == element);
            }
        }
    }

    true
}

} // verus!