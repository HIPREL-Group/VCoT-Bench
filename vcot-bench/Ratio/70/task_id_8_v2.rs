use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_vec_len_view_eq<T>(v: &Vec<T>)
    

#[verifier::exec_allows_no_decreases_clause]
fn square_nums(nums: &Vec<i32>) -> (squared: Vec<i32>)
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
    ensures
        nums.len() == squared.len(),
        forall|k: int| 0 <= k < nums.len() ==> (#[trigger] squared[k] == nums[k] * nums[k]),
{
    let mut result: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < nums.len()
        invariant
            0 <= index <= nums.len(),
            result@.len() == index,
            forall|k: int|
                0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
            forall|k: int| 0 <= k < index ==> (#[trigger] result[k] == nums[k] * nums[k]),
    {
        let val = nums[index] * nums[index];

        let ghost old_result = result@;
        let ghost old_index: int = (index as int);

        result.push(val);

        // Fill in a block of assertions here to complete the proof

        index += 1
    }

    result
}

} // verus!