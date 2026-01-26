use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_extend_prefix_parity(arr: &Vec<usize>, index: usize)
    requires
        index < arr.len(),
        forall|i: int| 0 <= i < index as int ==> ((i % 2) == (arr[i] % 2)),
        ((index as int) % 2) == (arr[index as int] % 2),
    ensures
        forall|i: int| 0 <= i < (index as int + 1) ==> ((i % 2) == (arr[i] % 2)),
{
    assert forall|i: int| 0 <= i < (index as int + 1) implies ((i % 2) == (arr[i] % 2)) by {
        let i = i;

        if i < index as int {
            assert((i % 2) == (arr[i] % 2));
        } else {
            assert(i == index as int);
            assert((i % 2) == (arr[i] % 2));
        }
    }
}

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
            assert(!forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2))) by {
                let wit: int = index as int;
                assert(wit < arr.len());
                assert(!((wit % 2) == (arr[wit] % 2)));
            }

            return false;
        }

        assert(((index as int) % 2) == (arr[index as int] % 2));

        proof {
            lemma_extend_prefix_parity(arr, index);
        }

        index += 1;
    }

    // Fill in a block of assertions here to complete the proof

    true
}

} // verus!