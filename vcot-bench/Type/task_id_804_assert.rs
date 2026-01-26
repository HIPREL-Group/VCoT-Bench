use vstd::prelude::*;
fn main() {
}

verus! {

spec fn is_even(n: u32) -> bool {
    (n % 2) == 0
}

proof fn lemma_forall_split_at_index(arr: &Vec<u32>, index: int)
    requires
        0 <= index < arr.len(),
        forall|k: int| 0 <= k < index ==> !(is_even(#[trigger] arr[k])),
        !(is_even(arr[index])),
    ensures
        forall|k: int| 0 <= k < index + 1 ==> !(is_even(#[trigger] arr[k])),
{
    assert(forall|k: int| 0 <= k < index + 1 ==> !(is_even(#[trigger] arr[k]))) by {
        assert forall|k: int| 0 <= k < index + 1 implies !(is_even(#[trigger] arr[k])) by {
            if k < index {
                assert(0 <= k < index);
                assert(!(is_even(arr[k])));
            } else {
                assert(!(k < index));
                assert(k == index);
                assert(!(is_even(arr[index])));
            }
        }
    }
}

proof fn lemma_forall_prefix_from_index_plus_1(
    arr: &Vec<u32>,
    old_index: int,
    new_index: int,
)
    requires
        0 <= old_index,
        new_index == old_index + 1,
        forall|k: int| 0 <= k < old_index + 1 ==> !(is_even(#[trigger] arr[k])),
    ensures
        forall|k: int| 0 <= k < new_index ==> !(is_even(#[trigger] arr[k])),
{
    assert forall|k: int| 0 <= k < new_index implies !(is_even(#[trigger] arr[k])) by {
        assert(0 <= k < old_index + 1);
        assert(!(is_even(arr[k])));
    }
}

proof fn lemma_not_exists_from_forall_not(
    arr: &Vec<u32>,
    n: int,
)
    requires
        n == arr.len(),
        forall|k: int| 0 <= k < n ==> !(is_even(#[trigger] arr[k])),
    ensures
        !(exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
{
    assert(!(exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k]))) by {
        assert forall|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k]) implies false by {
            assert(0 <= k < n);
            assert(!(is_even(arr[k])));
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn is_product_even(arr: &Vec<u32>) -> (result: bool)
    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
{
    let mut index = 0;

    // Fill in a block of assertions here to complete the proof

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|k: int| 0 <= k < index ==> !(is_even(#[trigger] arr[k])),
    {
        if (arr[index] % 2 == 0) {
            // Fill in a block of assertions here to complete the proof

            return true;
        }

        // Fill in a block of assertions here to complete the proof

        let old_index = index;
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof

    false
}

} // verus!