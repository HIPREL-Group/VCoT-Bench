use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_push_preserves_prefix_cube(
    nums: &Vec<i32>,
    old: Seq<i32>,
    new: Seq<i32>,
    i: int,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn cube_element(nums: &Vec<i32>) -> (cubed: Vec<i32>)
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                <= i32::MAX),
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                * #[trigger] nums[k] <= i32::MAX),
    ensures
        forall|i: int|
            0 <= i < nums.len() ==> cubed[i] == #[trigger] nums[i] * #[trigger] nums[i]
                * #[trigger] nums[i],
{
    let mut cubed_array: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < nums.len()
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof

        let ghost old_view = cubed_array@;
        cubed_array.push(nums[i] * nums[i] * nums[i]);
        let ghost new_view = cubed_array@;

        // Fill in a block of assertions here to complete the proof

        i += 1;
    }

    // Fill in a block of assertions here to complete the proof

    cubed_array
}

}