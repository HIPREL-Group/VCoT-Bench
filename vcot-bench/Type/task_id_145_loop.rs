use vstd::prelude::*;

fn main() {
}

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn max_difference(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= diff,
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];

    let mut index = 1;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] < min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    proof {
        assert(index == arr.len());

        assert(forall|i: int| 0 <= i < arr.len() ==> min_val <= arr[i] && arr[i] <= max_val) by {
            assert(forall|k: int| 0 <= k < index ==> min_val <= arr[k] && arr[k] <= max_val);
            assert(index == arr.len());
        };

        assert(forall|i: int, j: int|
            0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= max_val - min_val) by {
            assert(forall|t: int| 0 <= t < arr.len() ==> min_val <= arr[t] && arr[t] <= max_val);
        };

        assert(i32::MIN / 2 < min_val < i32::MAX / 2);
        assert(i32::MIN / 2 < max_val < i32::MAX / 2);

        assert(max_val - min_val <= (i32::MAX / 2) - (i32::MIN / 2));
        assert((i32::MAX / 2) - (i32::MIN / 2) <= (i32::MAX as int));
        assert(max_val - min_val >= (i32::MIN as int));
        assert(max_val - min_val <= (i32::MAX as int));
    }

    max_val - min_val
}

} // verus!