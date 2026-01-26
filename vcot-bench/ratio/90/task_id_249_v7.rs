use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_range_extend<T>(
    s: Seq<T>,
    key: T,
    i: int,
    j: int,
)
   

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
            proof {
                assert(exists|k: int| 0 <= k < arr.len() && arr[k] == key) by {
                    assert(0 <= (i as int) && i < arr.len() && arr[(i as int)] == key);
                }
            }
            return true;
        }
        // Fill in a block of assertions here to complete the proof
        i += 1;
    }
    // Fill in a block of assertions here to complete the proof
    false
}

#[verifier::exec_allows_no_decreases_clause]
fn intersection(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut output_arr = Vec::new();

    let mut index = 0;
    while index < arr1.len()
        // Fill in loop invariants here
    {
        let ghost x = arr1[(index as int)];
        let in_arr2 = contains(arr2, arr1[index]);
        let in_output = contains(&output_arr, arr1[index]);
        
        if (in_arr2 && !in_output) {
            // Fill in a block of assertions here to complete the proof

            let ghost old_len: int = output_arr.len() as int;
            let ghost old_output_arr = output_arr@;
            output_arr.push(arr1[index]);

            // Fill in a block of assertions here to complete the proof
        }
        index += 1;
    }
    output_arr
}

} // verus!