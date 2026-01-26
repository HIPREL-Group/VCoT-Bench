use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_forall_split_lt_index_to_lt_index_plus_1(arr: &Vec<i32>, k: i32, index: int)
    requires
        0 <= index,
        index < arr.len(),
        forall|m: int| 0 <= m < index ==> (arr[m] != k),
        arr[index] != k,
    ensures
        forall|m: int| 0 <= m < index + 1 ==> (arr[m] != k),
{
    assert forall|m: int| 0 <= m < index + 1 implies (arr[m] != k) by {
        if m < index {
            assert(arr[m] != k);
        } else {
            assert(m == index);
            assert(arr[m] != k);
        }
    };
}

// Complete the lemma function below
proof fn lemma_forall_implies_not_exists<T>(p: spec_fn(T) -> bool)
    

#[verifier::exec_allows_no_decreases_clause]
fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
{
    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] == k) {
            // Fill in a block of assertions here to complete the proof;
            return true;
        }
        assert(arr[(index as int)] != k);

        proof {
            lemma_forall_split_lt_index_to_lt_index_plus_1(arr, k, (index as int));
        }

        index += 1;
    }

    // Fill in a block of assertions here to complete the proof;

    false
}

} // verus!