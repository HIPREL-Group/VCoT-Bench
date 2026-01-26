use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_extend_mod2_invariant_forall(
    arr: &Vec<usize>,
    old_index: usize,
)
    requires
        0 <= old_index <= arr.len(),
        forall|i: int| 0 <= i < old_index ==> (i % 2 == arr[i] % 2),
        old_index < arr.len(),
        (old_index % 2) == (arr[(old_index as int)] % 2),
    ensures
        forall|i: int| 0 <= i < old_index + 1 ==> (i % 2 == arr[i] % 2),
{
    assert(forall|i: int| 0 <= i < old_index + 1 ==> (i % 2 == arr[i] % 2)) by {
        assert forall|i: int| 0 <= i < old_index + 1 implies (i % 2 == arr[i] % 2) by {
            if i < old_index {
                assert(i % 2 == arr[i] % 2);
            } else {
                assert(i == old_index as int) by {
                    assert(i <= old_index as int);
                    assert(old_index as int <= i);
                }
                assert((old_index as int) % 2 == (arr[old_index as int] % 2)) by {
                    assert((old_index % 2) == (arr[(old_index as int)] % 2));
                }
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof;

        if ((index % 2) != (arr[index] % 2)) {
            assert(((index as int) % 2) != (arr[index as int] % 2)) by {
                assert((index as int) % 2 == (index % 2) as int);
                assert((arr[index as int] % 2) == ((arr[(index as int)] % 2) as int));
            }
            return false;
        } else {
            assert((index % 2) == (arr[(index as int)] % 2));
            assert(((index as int) % 2) == (arr[index as int] % 2)) by {
                assert((index as int) % 2 == (index % 2) as int);
                assert((arr[index as int] % 2) == ((arr[(index as int)] % 2) as int));
            }
        }

        let old_index = index;
        index += 1;

        proof {
            lemma_extend_mod2_invariant_forall(arr, old_index);
        }

        assert(forall|i: int|
            0 <= i < index ==> ((i % 2) == (arr[i] % 2))
        );
    }
    assert(index == arr.len());
    assert(forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2))) by {
        assert(forall|i: int| 0 <= i < index ==> ((i % 2) == (arr[i] % 2)));
    }
    true
}

} // verus!