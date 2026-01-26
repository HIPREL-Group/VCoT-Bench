use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_step_sum_bound(prev_sum: int, a_i: int, i: int)
   

// Complete the lemma function below
proof fn lemma_forall_extend_by_new_index_i32(a: &Vec<i32>, i: usize)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 3 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		a.set(i, (i % 4) as i32);

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		// Fill in loop invariants here
	{
		if (i == 0) {
			sum.set(0, 0);
			// Fill in a block of assertions here to complete the proof;
		} else {
			// Fill in a block of assertions here to complete the proof

			let temp = sum[0] + a[i];

			// Fill in a block of assertions here to complete the proof;

			sum.set(0, temp);

			// Fill in a block of assertions here to complete the proof;
		}

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;

		// Fill in a block of assertions here to complete the proof;
	}

	// Fill in a block of assertions here to complete the proof;

	if i > 0 {
		// Fill in a block of assertions here to complete the proof;
	}
	// Fill in a block of assertions here to complete the proof;
}
}