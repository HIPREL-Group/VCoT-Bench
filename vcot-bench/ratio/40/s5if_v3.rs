use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_mul5_succ(i: int)
    ensures
        5 * (i + 1) == 5 * i + 5
{
    assert(5 * (i + 1) == 5 * i + 5) by (nonlinear_arith);
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 5 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			forall |k:int| 0<= k < i ==> a[k] == 5,
			a.len() == N,
	{
		a.set(i, 5);

		// Fill in a block of assertions here to complete the proof

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0<= k < N ==> a[k] == 5,
			a.len() == N,
			sum[0] == 5 * i,
			sum.len() == 1,
			N < 1000,
	{
		// Fill in a block of assertions here to complete the proof

		if (a[i] == 5) {
			let temp = sum[0] + a[i];
			assert(a[(i as int)] == 5);
			assert(sum[0] == 5 * (i as int));

			proof {
				lemma_mul5_succ(i as int);
			}

			sum.set(0, temp);

			// Fill in a block of assertions here to complete the proof
		} else {
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}

		i = i + 1;
	}

	assert(sum[0] == 5 * N) by {
		assert(!(i < N as usize));
		assert(i <= N as usize);
	}
}
}