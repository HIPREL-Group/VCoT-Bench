use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_extend_mod2_invariant_forall(
    arr: &Vec<usize>,
    old_index: usize,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> ((i % 2) == (arr[i] % 2)),
    {
        // Fill in a block of assertions here to complete the proof;

        if ((index % 2) != (arr[index] % 2)) {
            assert(((index as int) % 2) != (arr[index as int] % 2)) by {
                assert((index as int) % 2 == (index % 2) as int);
                assert((arr[index as int] % 2) == ((arr[(index as int)] % 2) as int));
            }
            return false;
        } else {
            // Fill in a block of assertions here to complete the proof
        }

        let old_index = index;
        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }
    // Fill in a block of assertions here to complete the proof
    true
}

} // verus!