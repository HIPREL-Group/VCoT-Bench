use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_push_preserves_prefix_cube(
    nums: &Vec<i32>,
    old: Seq<i32>,
    new: Seq<i32>,
    i: int,
)
    requires
        0 <= i,
        new.len() == i + 1,
        old.len() == i,
        new.subrange(0, i) == old,
        forall|k: int| 0 <= k < i ==> old[k] == nums[k] * nums[k] * nums[k],
        new[i] == nums[i] * nums[i] * nums[i],
    ensures
        forall|k: int| 0 <= k < i + 1 ==> new[k] == nums[k] * nums[k] * nums[k],
{
    assert forall|k: int| 0 <= k < i + 1 implies new[k] == nums[k] * nums[k] * nums[k] by {
        if k < i {
            assert(new[k] == old[k]) by {
                assert(new.subrange(0, i) == old);
            }
            assert(old[k] == nums[k] * nums[k] * nums[k]);
        } else {
            assert(k == i);
            assert(new[k] == new[i]);
        }
    }
}

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
        invariant
            0 <= i <= nums.len(),
            cubed_array@.len() == i,
            forall|k: int|
                0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                    <= i32::MAX),
            forall|k: int|
                0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                    * #[trigger] nums[k] <= i32::MAX),
            forall|k: int|
                0 <= k < i ==> (#[trigger] cubed_array[k] == nums[k] * nums[k] * nums[k]),
    {
        assert(i < nums.len());

        assert(i32::MIN <= nums[(i as int)] * nums[(i as int)] * nums[(i as int)] && nums[(i as int)] * nums[(i as int)] * nums[(i as int)] <= i32::MAX) by {
            assert(forall|k: int|
                0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                    * #[trigger] nums[k] <= i32::MAX));
        }

        let ghost old_view = cubed_array@;
        cubed_array.push(nums[i] * nums[i] * nums[i]);
        let ghost new_view = cubed_array@;

        assert(cubed_array@.len() == i + 1);

        assert(new_view.subrange(0, (i as int)) =~= old_view);

        assert(forall|k: int|
            0 <= k < (i as int) + 1 ==> (#[trigger] cubed_array[k] == nums[k] * nums[k] * nums[k])) by {
            lemma_push_preserves_prefix_cube(nums, old_view, new_view, (i as int));
        }

        i += 1;
    }

    // Fill in a block of assertions here to complete the proof

    cubed_array
}

}