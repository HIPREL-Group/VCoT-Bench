use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_extend_prefix_parity(arr: &Vec<usize>, index: usize)
   

#[verifier::exec_allows_no_decreases_clause]
fn is_odd_at_odd_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> ((i % 2) == (arr[i] % 2)),
    {
        if ((index % 2) != (arr[index] % 2)) {
            // Fill in a block of assertions here to complete the proof

            return false;
        }

        assert(((index as int) % 2) == (arr[index as int] % 2));

        proof {
            lemma_extend_prefix_parity(arr, index);
        }

        index += 1;
    }

    assert(forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2))) by {
        assert forall|i: int| 0 <= i < arr.len() implies ((i % 2) == (arr[i] % 2)) by {
            let i = i;
            if 0 <= i < arr.len() {
                assert(i < index);
                assert((i % 2) == (arr[i] % 2));
            }
        }
    }

    true
}

} // verus!