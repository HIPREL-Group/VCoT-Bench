use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_i32_add_overflow_free_for_sum_progress(i: int, n: int)
   

// Complete the lemma function below
proof fn lemma_forall_extend_by_last_set_to_2(a_old: Seq<i32>, i_old: int, idx_set: int)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
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
	while (i < N as usize)
		// Fill in loop invariants here
	{
		// Fill in a block of assertions here to complete the proof;

		let ghost old_view = a@;
		// Fill in a block of assertions here to complete the proof

		a.set(i, 2);

		let ghost new_view = a@;
		// Fill in a block of assertions here to complete the proof;

		let ghost i_old: int = (i as int);
		i = i + 1;

		// Fill in a block of assertions here to complete the proof
	}

	// Fill in a block of assertions here to complete the proof

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		// Fill in a block of assertions here to complete the proof;

		assert(a[(i as int)] == 2) by {
			assert(0 <= (i as int));
			assert((i as int) < (N as int)) by {
				assert(i < N as usize);
			}
			assert(a[i as int] == 2);
		}

		if (a[i] == 2) {
            // Fill in a block of assertions here to complete the proof

			let sum_before_set = sum[0];
			let temp = sum[0] + a[i];

			// Fill in a block of assertions here to complete the proof;

			let ghost sum_view_before = sum@;
			// Fill in a block of assertions here to complete the proof;

			sum.set(0, temp);

			let ghost sum_view_after = sum@;
			// Fill in a block of assertions here to complete the proof;
		} else {
			// Fill in a block of assertions here to complete the proof
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}

		let iprev_usize = i;
		i = i + 1;

		// Fill in a block of assertions here to complete the proof
	}

	// Fill in a block of assertions here to complete the proof;
}
}