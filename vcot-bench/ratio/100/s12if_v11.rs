use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_forall_set_singleton_push(
    a: &Vec<i32>,
    i: usize,
)
   

// Complete the lemma function below
proof fn lemma_forall_update_preserves_prefix_ones(
    a_before: &Vec<i32>,
    a_after: &Vec<i32>,
    i: usize,
)
   

// Complete the lemma function below
proof fn lemma_forall_update_preserves_prefix_twos(
    a_before: &Vec<i32>,
    a_after: &Vec<i32>,
    i: usize,
)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 2 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N)
		// Fill in loop invariants here
	{
		let ghost old_a = *a;

		a.set(i, 1);

		// Fill in a block of assertions here to complete the proof

		i = i + 1;
	}

	i = 0;
	while (i < N)
		// Fill in loop invariants here
	{
		let ghost old_a = *a;

		if (a[i] == 1) {
			let temp = a[i];
			a.set(i, temp + 1);

			// Fill in a block of assertions here to complete the proof;
		} else {
			let temp = a[i];
			a.set(i, temp - 1);
		}

		// Fill in a block of assertions here to complete the proof

		i = i + 1;
	}

	i = 0;
	while (i < N)
		// Fill in loop invariants here
	{
		if (a[i] == 2) {
            let old_sum = sum[0];

			let temp = sum[0] + a[i];
			// Fill in a block of assertions here to complete the proof;

			sum.set(0, temp);

            // Fill in a block of assertions here to complete the proof;
		} else {
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}

		i = i + 1;
	}
}
}