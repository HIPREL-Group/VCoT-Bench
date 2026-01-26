use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_seq_update_extends_forall_prefix_1(old_s: Seq<i32>, new_s: Seq<i32>, i0: int)
   

// Complete the lemma function below
proof fn lemma_vec_set_view_update_i32(v: &Vec<i32>, i: usize, val: i32)
   

// Complete the lemma function below
proof fn lemma_second_loop_if_branch_sets_i_to_6(a: &Vec<i32>, i: usize)
   

// Complete the lemma function below
proof fn lemma_second_loop_else_branch_sets_i_to_5(a: &Vec<i32>, i: usize)
   

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
		// Fill in loop invariants here
	{
		let old_view = Ghost(a@);
		a.set(i, 1);

        // Fill in a block of assertions here to complete the proof;

		i = i + 1;

        // Fill in a block of assertions here to complete the proof
	}

	i = 0;
	while (i < N)
		// Fill in loop invariants here
	{
		if (a[i] == 1) {
			let temp = a[i];
            // Fill in a block of assertions here to complete the proof
			a.set(i, temp + 5);
		} else {
			let temp = a[i];
            // Fill in a block of assertions here to complete the proof
			a.set(i, temp - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N)
		invariant
			i <= N,
			forall |k:int| 0 <= k < N ==> a[k] == 6,
			a.len() == N,
			sum[0] == 6 * i,
			sum.len() == 1,
			N < 1000,
	{
		// Fill in a block of assertions here to complete the proof;

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

		// Fill in a block of assertions here to complete the proof;
	}

	// Fill in a block of assertions here to complete the proof;
}
}