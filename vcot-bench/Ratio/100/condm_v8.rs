use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_mod2_add_1(x: int)
    

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, N: u32)
	requires
		N > 0,
		old(a).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] % 2 == N % 2,
{
	let mut i: usize = 0;

	while (i < N as usize)
		// Fill in loop invariants here
	{
		a.set(i, 0);

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		if (N % 2 == 0) {
            let temp = a[i];
            // Fill in a block of assertions here to complete the proof

			a.set(i, temp + 2);

            // Fill in a block of assertions here to complete the proof
		} else {
            let temp = a[i];
            // Fill in a block of assertions here to complete the proof

			a.set(i, temp + 1);

            // Fill in a block of assertions here to complete the proof
		}

        // Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}
}
}