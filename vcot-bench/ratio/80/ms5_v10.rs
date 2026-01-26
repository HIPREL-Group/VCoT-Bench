use vstd::prelude::*;
fn main() {}

verus!{

// Complete the lemma function below
proof fn lemma_mod5_i32_bounds(i: usize)
    

proof fn lemma_extend_sum_bound(sum_prev: int, a_i: int, i: int)
    requires
        i > 0,
        sum_prev <= 4 * i,
        0 <= a_i <= 4,
    ensures
        sum_prev + a_i <= 4 * (i + 1),
{
}

// Complete the lemma function below
proof fn lemma_usize_from_i32_nonneg_and_lt_1000_implies_no_overflow(N: i32)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 4 * N,
{
    // Fill in a block of assertions here to complete the proof

	let mut i: usize = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
        // Fill in a block of assertions here to complete the proof

		a.set(i, (i % 5) as i32);

        i = i + 1;

        // Fill in a block of assertions here to complete the proof
	}

	i = 0;
	
	while (i < N as usize)
		// Fill in loop invariants here
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
            // Fill in a block of assertions here to complete the proof

			let temp = sum[0] + a[i];
			sum.set(0, temp);

            assert(sum[0] as int <= 4 * ((i as int) + 1)) by {
                if i > 0 {
                    let prev_sum = (sum[0] as int) - (a[(i as int)] as int);
                    assert(prev_sum <= 4 * (i as int));
                    lemma_extend_sum_bound(prev_sum, a[(i as int)] as int, (i as int));
                }
            }
		}
		i = i + 1;

        if i > 0 {
            // Fill in a block of assertions here to complete the proof
        }
	}

    // Fill in a block of assertions here to complete the proof;
}
}