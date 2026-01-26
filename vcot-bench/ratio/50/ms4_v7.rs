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

		assert(a[i as int] == (i as int) % 4) by {
		    assert((i % 4) as int == (i as int) % 4) by (nonlinear_arith);
		    assert(a[(i as int)] == (i % 4) as i32);
		}

		assert(forall |k:int| 0<= k < (i + 1) ==> a[k] == k % 4) by {
			assert(a[i as int] == (i as int) % 4);
			lemma_forall_extend_by_new_index_i32(a, i);
		};

		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			i <= N,
			i>0 ==> sum[0] <= 3 * i,
			sum.len() == 1,
			forall |k:int| 0<= k < N ==> a[k] == k % 4,
			a.len() == N,
			N < 1000,
	{
		if (i == 0) {
			sum.set(0, 0);
			assert(sum[0] == 0);

			// Fill in a block of assertions here to complete the proof;
		} else {
			// Fill in a block of assertions here to complete the proof

			let temp = sum[0] + a[i];

			assert(sum[0] + a[(i as int)] <= 3 * (i as int + 1)) by {
				let prev_sum: int = sum[0] as int;
				let ai: int = a[(i as int)] as int;

				assert(prev_sum <= 3 * (i as int)) by {
					assert(sum[0] <= 3 * i);
				}
				assert(0 <= ai) by { assert(0 <= a[(i as int)]); }
				assert(ai <= 3) by { assert(a[(i as int)] <= 3); }
				lemma_step_sum_bound(prev_sum, ai, i as int);
			};

			sum.set(0, temp);

			assert(sum[0] as int <= 3 * ((i as int) + 1));
		}

		assert(i + 1 <= N);

		i = i + 1;

		// Fill in a block of assertions here to complete the proof;
	}

	assert(i == N as usize);

	if i > 0 {
		// Fill in a block of assertions here to complete the proof;
	}
	// Fill in a block of assertions here to complete the proof;
}
}