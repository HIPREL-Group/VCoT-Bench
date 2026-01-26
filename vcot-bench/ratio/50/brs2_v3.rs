use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_a_elem_bound(a: &Vec<i32>, k: int)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 2 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			forall |k:int| 0<= k < i ==> a[k] == 2 || a[k] == 0,
			a.len() == N,
	{
		if (i % 2 == 0) {
			a.set(i, 2);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		// Fill in loop invariants here
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			let temp = sum[0];

            // Fill in a block of assertions here to complete the proof;

			sum.set(0, temp + a[i]);
		}
		i = i + 1;
	}

	assert(i == N as usize);
	if i > 0 {
		assert(sum[0] <= 2 * (i as int));
	}
}
}