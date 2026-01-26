use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_vec_set_invariant_0_or_5(
    a_before: &Vec<i32>,
    a_after: &Vec<i32>,
    i: usize,
    v: i32,
)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 5 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		if (i % 5 == 0) {
			a.set(i, 5);
		} else {
			a.set(i, 0);
		}

        // Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		// Fill in loop invariants here
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
            let ai: i32 = a[i];
            let temp = sum[0];

			sum.set(0, temp + a[i]);

            // Fill in a block of assertions here to complete the proof
		}

		i = i + 1;
	}

    // Fill in a block of assertions here to complete the proof;
}
}