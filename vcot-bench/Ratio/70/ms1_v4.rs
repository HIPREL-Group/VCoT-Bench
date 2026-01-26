use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_forall_extend_one(a: &Vec<usize>, i: usize, v: usize)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
	ensures
		sum[0] == 0,
{
	let mut i: usize = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
        let tmp: usize = i % 1;
        // Fill in a block of assertions here to complete the proof;

		a.set(i, tmp);

        // Fill in a block of assertions here to complete the proof

		i = i + 1;
	}

	i = 0;

	while (i < N as usize)
		invariant
			forall |k: int| 0<= k < N ==> a[k] == 0,
			a.len() == N,
			i > 0 ==> sum[0] == 0,
			sum.len() == 1,
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
            let temp = sum[0] + a[i];
            assert(temp == sum[0]);
			sum.set(0, temp);
		}
		i = i + 1;
	}
}
}