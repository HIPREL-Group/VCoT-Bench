use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_step_sum_bound(prev_sum: int, a_i: int, i: int)
    requires
        i > 0,
        prev_sum <= 3 * i,
        0 <= a_i,
        a_i <= 3,
    ensures
        prev_sum + a_i <= 3 * (i + 1)
{
    assert(prev_sum + a_i <= 3 * i + 3);
    assert(3 * i + 3 == 3 * (i + 1)) by (nonlinear_arith);
}

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
		// Fill in loop invariants here
	{
		if (i == 0) {
			sum.set(0, 0);
			// Fill in a block of assertions here to complete the proof;
		} else {
			assert(0 <= a[(i as int)]) by {
				assert(0 <= (i as int) % 4) by (nonlinear_arith);
				assert(a[i as int] == (i as int) % 4);
				assert(0 <= a[(i as int)] as int);
			}
			assert(a[(i as int)] <= 3) by {
				assert((i as int) % 4 <= 3) by (nonlinear_arith);
				assert(a[i as int] == (i as int) % 4);
				assert(a[(i as int)] as int <= 3);
			}

			let temp = sum[0] + a[i];

			// Fill in a block of assertions here to complete the proof;

			sum.set(0, temp);

			// Fill in a block of assertions here to complete the proof;
		}

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;

		assert(i <= N);
	}

	assert(i == N as usize);

	if i > 0 {
		assert(sum[0] <= 3 * (i as i32));
	}
	// Fill in a block of assertions here to complete the proof;
}
}