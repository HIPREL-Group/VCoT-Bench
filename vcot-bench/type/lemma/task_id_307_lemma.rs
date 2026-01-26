use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_seq_push_preserves_prefix_u64(s: Seq<u64>, x: u64)
    

#[verifier::exec_allows_no_decreases_clause]
fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)
    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
{
    let mut copied_array = Vec::with_capacity(arr.len());
    let mut index = 0;

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            copied_array.len() == index,
            forall|i: int| (0 <= i < index) ==> arr[i] == copied_array[i],
    {
        let ghost old_copied_view = copied_array@;
        let x = arr[index];

        copied_array.push(x);

        assert(copied_array@ == old_copied_view.push(x));

        assert(copied_array.len() == index + 1);

        assert forall|i: int| (0 <= i < index) implies arr[i] == copied_array[i] by {
            assert(arr[i] == old_copied_view[i]);
            assert(old_copied_view[i] == old_copied_view.push(x)[i]) by {
                lemma_seq_push_preserves_prefix_u64(old_copied_view, x);
            }
        }

        assert(arr[(index as int)] == copied_array@[(index as int)]);

        index += 1;

        assert(copied_array.len() == index);
    }

    assert(index == arr.len());
    assert(copied_array.len() == arr.len());
    assert(arr@.len() == copied_array@.len());

    assert forall|i: int| (0 <= i < arr.len()) implies arr[i] == copied_array[i] by {
        assert(0 <= i < index);
        assert(arr[i] == copied_array[i]);
    }

    copied_array
}

} // verus!