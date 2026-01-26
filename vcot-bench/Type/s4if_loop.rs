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
		sum[0] == 4 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		a.set(i, 4);

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		if (a[i] == 4) {
			let temp = sum[0] + a[i];
			sum.set(0, temp);
		} else {
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}

		i = i + 1;
	}

	assert(i == N as usize);
	assert(sum[0] == 4 * (N as int));
}
}