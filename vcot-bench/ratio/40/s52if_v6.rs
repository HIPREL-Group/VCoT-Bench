use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_seq_update_extends_forall_prefix_1(old_s: Seq<i32>, new_s: Seq<i32>, i0: int)
   

// Complete the lemma function below
proof fn lemma_vec_set_view_update_i32(v: &Vec<i32>, i: usize, val: i32)
   

proof fn lemma_second_loop_if_branch_sets_i_to_6(a: &Vec<i32>, i: usize)
    requires
        i < a.len(),
        a[(i as int)] == 1,
    ensures
        a@.update((i as int), (a[(i as int)] + 5) as i32)[(i as int)] == 6,
{
}

proof fn lemma_second_loop_else_branch_sets_i_to_5(a: &Vec<i32>, i: usize)
    requires
        i < a.len(),
        a[(i as int)] == 6,
    ensures
        a@.update((i as int), (a[(i as int)] - 1) as i32)[(i as int)] == 5,
{
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 6 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N)
		invariant
			forall |k:int| 0 <= k < i ==> a[k] == 1,
			a.len() == N,
	{
		let old_view = Ghost(a@);
		a.set(i, 1);

        // Fill in a block of assertions here to complete the proof;

		i = i + 1;

        // Fill in a block of assertions here to complete the proof
	}

	i = 0;
	while (i < N)
		invariant
			forall |k:int| 0 <= k < i ==> a[k] == 6,
			forall |k:int| i <= k < N ==> a[k] == 1,
			a.len() == N,
	{
		if (a[i] == 1) {
			let temp = a[i];
            // Fill in a block of assertions here to complete the proof
			a.set(i, temp + 5);
		} else {
			let temp = a[i];
            proof {
			    lemma_second_loop_else_branch_sets_i_to_5(a, i);
            }
			a.set(i, temp - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N)
		// Fill in loop invariants here
	{
		assert(a[(i as int)] == 6);

		if (a[i] == 6)
		{
			let temp = sum[0] + a[i];
			sum.set(0, temp);
			assert(sum[0] == 6 * (i + 1)) by {
				assert(6 * (i + 1) == 6 * i + 6);
			}
		} else {
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}
		i = i + 1;

		assert(sum[0] == 6 * i);
	}

	assert(sum[0] == 6 * N);
}
}