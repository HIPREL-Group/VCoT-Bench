use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_u32_sum_lt_256_implies_no_overflow(a: u32, b: u32)
    requires
        (a as int) + (b as int) < 256,
    ensures
        a + b == a + b,
{
}

proof fn lemma_u32_add_lt_256_implies_not_overflowing_sum_is_int_sum(a: u32, b: u32)
    requires
        (a as int) + (b as int) < 256,
    ensures
        ((a + b) as int) == (a as int) + (b as int),
{
    lemma_u32_sum_lt_256_implies_no_overflow(a, b);
    assert(((a + b) as int) == (a as int) + (b as int));
}

proof fn lemma_forall_split_row_prefix(
    nums: &Vec<u32>,
    target: u32,
    i: usize,
    j: usize,
)
    requires
        forall|ii: int, jj: int|
            (0 <= ii && ii < (i as int) && ii < jj && jj < (nums.len() as int)) ==> nums[ii] + nums[jj] != target,
        forall|jj2: int|
            ((i as int) < jj2 && jj2 < (j as int)) ==> nums[(i as int)] + nums[jj2] != target,
    ensures
        forall|ii2: int, jj2: int|
            ((0 <= ii2 && ii2 < (i as int) && ii2 < jj2 && jj2 < (nums.len() as int))
                || (ii2 == (i as int) && ii2 < jj2 && jj2 < (j as int)))
            ==> nums[ii2] + nums[jj2] != target,
{
}

proof fn lemma_forall_extend_row_prefix(
    nums: &Vec<u32>,
    target: u32,
    i: usize,
    j: usize,
)
    requires
        forall|jj2: int| ((i as int) < jj2 && jj2 < (j as int)) ==> nums[(i as int)] + nums[jj2] != target,
        nums[(i as int)] + nums[(j as int)] != target,
    ensures
        forall|jj2: int| ((i as int) < jj2 && jj2 < ((j + 1) as int)) ==> nums[(i as int)] + nums[jj2] != target,
{
}

proof fn lemma_forall_extend_matrix_prefix(
    nums: &Vec<u32>,
    target: u32,
    i: usize,
    n: usize,
)
    requires
        forall|ii: int, jj2: int|
            (0 <= ii && ii < (i as int) && ii < jj2 && jj2 < (n as int)) ==> nums[ii] + nums[jj2] != target,
        forall|jj2: int|
            ((i as int) < jj2 && jj2 < (n as int)) ==> nums[(i as int)] + nums[jj2] != target,
    ensures
        forall|ii: int, jj2: int|
            (0 <= ii && ii < ((i + 1) as int) && ii < jj2 && jj2 < (n as int)) ==> nums[ii] + nums[jj2] != target,
{
}

#[verifier::exec_allows_no_decreases_clause]
fn two_sum(nums: &Vec<u32>, target: u32) -> (r: (usize, usize))
    requires
        nums.len() > 1,
        forall|ii: int, jj: int|
            ((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj]
                < 256,
        exists|i: int, j: int| (0 <= i && i < j && j < nums.len()) && nums[i] + nums[j] == target,
    ensures
        (0 <= r.0 && r.0 < r.1 && r.1 < nums.len()) && nums[(r.0 as int)] + nums[(r.1 as int)]
            == target,
        forall|ii: int, jj: int|
            ((0 <= ii && ii < r.0 && ii < jj && jj < nums.len()) || (ii == r.0 && ii < jj && jj
                < r.1)) ==> nums[ii] + nums[jj] != target,
{
    let n = nums.len();
    let mut i = 0;
    let mut j = 1;

    proof {
        assert(n == nums@.len());
        assert(0 <= i && i < j && j <= n);
    }

    while i < n - 1
        // Fill in loop invariants here
    {
        j = i + 1;

        while j < n
            invariant
                n == nums@.len(),
                0 <= i && i < j && j <= n,
                forall|ii: int, jj: int|
                    ((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii]
                        + nums[jj] < 256,
                forall|ii: int, jj: int|
                    (0 <= ii && ii < i && ii < jj && jj < n) ==> nums[ii] + nums[jj] != target,
                forall|jj: int| (i < jj && jj < j) ==> nums[(i as int)] + nums[jj] != target,
        {
            proof {
                assert(nums[(i as int)] + nums[(j as int)] < 256) by {
                    assert(
                        ((0 <= (i as int) && (i as int) < nums.len() && (i as int) < (j as int) && (j as int) < nums.len()))
                    );
                };

                lemma_u32_add_lt_256_implies_not_overflowing_sum_is_int_sum(nums[(i as int)], nums[(j as int)]);
                assert(((nums[(i as int)] + nums[(j as int)]) as int) == (nums[(i as int)] as int) + (nums[(j as int)] as int));
            }

            if nums[i] + nums[j] == target {
                proof {
                    lemma_forall_split_row_prefix(nums, target, i, j);
                }
                return (i, j);
            }

            // Fill in a block of assertions here to complete the proof

            j += 1;
        }

        proof {
            lemma_forall_extend_matrix_prefix(nums, target, i, n);
        }

        i += 1;

        proof {
            assert(0 <= i && i < j && j <= n);
        }
    }
    (i, j)
}

} // verus!