use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_mod5_i32_bounds(i: usize)
    ensures
        0 <= (i % 5) as int,
        (i % 5) as int <= 4,
{
}

// Complete the lemma function below
proof fn lemma_extend_sum_bound(sum_prev: int, a_i: int, i: int)
   

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

        assert(forall |k:int| 0<= k < (i as int) ==> a[k] == k % 5) by {
            assert(forall |k:int| 0<= k < (i as int - 1) ==> a[k] == k % 5);
            assert(a[(i as int - 1)] == ((i as int - 1) % 5));
        }
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

            // Fill in a block of assertions here to complete the proof
		}
		i = i + 1;

        if i > 0 {
            assert(sum[0] <= 4 * (i as i32)) by {
                assert(sum[0] as int <= 4 * (i as int));
            }
        }
	}

    assert(i == N as usize);
    assert(sum[0] as int <= 4 * (N as int));
    assert(sum[0] <= 4 * N);
}
}