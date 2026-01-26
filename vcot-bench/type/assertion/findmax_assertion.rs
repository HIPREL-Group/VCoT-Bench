#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn find_max(nums: Vec<i32>) -> (ret:i32)
requires
    nums.len() > 0,
ensures
    forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
    exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
{
    let mut max = nums[0];
    let mut i = 1;

    // Fill in a block of assertions here to complete the proof

    while i < nums.len()
    invariant
        1 <= i <= nums.len(),
        forall |k: int| 0 <= k < i ==> nums@[k] <= max,
        exists |k: int| 0 <= k < i && nums@[k] == max,
    {
        if nums[i] > max {
            max = nums[i];
            // Fill in a block of assertions here to complete the proof
        } else {
            // Fill in a block of assertions here to complete the proof
        }

        i += 1;
    }

    // Fill in a block of assertions here to complete the proof

    max
}
}