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
		invariant
			forall |k:int| 0<= k < i ==> a[k] == 4,
			a.len() == N,
	{
		a.set(i, 4);

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0<= k < N ==> a[k] == 4,
			a.len() == N,
			sum[0] == 4 * i,
			sum.len() == 1,
			N < 1000,
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

	// Fill in a block of assertions here to complete the proof;
}
}