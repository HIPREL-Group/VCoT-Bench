use vstd::prelude::*;
fn main() {}
verus!{

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
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
        let temp = a[i];
		if (a[i] == 1) {
			a.set(i, temp + 1);
		} else {
			a.set(i, temp - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
        let temp = sum[0];

        // Fill in a block of assertions here to complete the proof;

        sum.set(0, temp + a[i]);

        i = i + 1;
	}

    // Fill in a block of assertions here to complete the proof;
}
}