use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_prefix_preserved<T>(
    s: Seq<T>,
    key: T,
    i: int,
    j: int,
)
   

// Complete the lemma function below
proof fn lemma_forall_prefix_extend<T>(
    s: Seq<T>,
    key: T,
    i: int,
)
   

// Complete the lemma function below
proof fn lemma_seq_contains_from_exec_contains(arr: &Vec<i32>, key: i32)
    

#[verifier::exec_allows_no_decreases_clause]
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        // Fill in loop invariants here
    {
        if (arr[i] == key) {
            return true;
        }
        // Fill in a block of assertions here to complete the proof
        i += 1;
    }
    // Fill in a block of assertions here to complete the proof
    false
}

#[verifier::exec_allows_no_decreases_clause]
fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
{
    let mut shared = Vec::new();
    let ghost mut shared_arr_len: int = 0;

    let mut index = 0;
    while index < list1.len()
        // Fill in loop invariants here
    {
        if (contains(list2, list1[index]) && !contains(&shared, list1[index])) {
            // Fill in a block of assertions here to complete the proof

            shared.push(list1[index]);

            // Fill in a block of assertions here to complete the proof
        }
        index += 1
    }
    shared
}

}