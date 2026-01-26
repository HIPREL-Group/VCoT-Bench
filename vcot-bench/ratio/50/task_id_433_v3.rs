use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_extend(arr: &Vec<i32>, number: i32, i: int)
   

// Complete the lemma function below
proof fn lemma_not_forall_from_counterexample(arr: &Vec<i32>, number: i32, j: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
    let mut i = 0;

    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> number > arr[k],
    {
        if number <= arr[i] {
            // Fill in a block of assertions here to complete the proof
            return false;
        }
        assert(number > arr[(i as int)]);

        proof {
            let ii: int = i as int;
            lemma_forall_extend(arr, number, ii);
        }

        i += 1;
    }

    assert(i == arr.len()) by {
        assert(!(i < arr.len()));
        assert(i <= arr.len());
        assert(arr.len() <= i) by {
            assert(i >= arr.len());
        }
    }

    assert(forall|k: int| 0 <= k < arr.len() ==> number > arr[k]) by {
        assert forall|k: int| 0 <= k < arr.len() implies number > arr[k] by {
            if 0 <= k < arr.len() {
                assert(0 <= k < i) by {
                    assert(i == arr.len());
                    assert(k < i);
                }
                assert(number > arr[k]);
            }
        }
    }
    true
}

} // verus!