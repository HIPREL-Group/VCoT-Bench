use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
pub proof fn lemma_forall_extend_one<T>(i: int, f: spec_fn(int) -> T, v: T)
   

// Complete the lemma function below
proof fn lemma_vec_set_extends_ones(v: &Vec<i32>, i: usize)
   

// Complete the lemma function below
proof fn lemma_vec_set_extends_ones_after_set(v: &Vec<i32>, i: usize)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(c).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] <= 3 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < (N as usize))
		// Fill in loop invariants here
	{
		a.set(i, 1);

		// Fill in a block of assertions here to complete the proof

		i = i + 1;
	}

	i = 0;
	while (i < (N as usize))
		// Fill in loop invariants here
	{
		b.set(i, 1);

		// Fill in a block of assertions here to complete the proof

		i = i + 1;
	}

	i = 0;
	while (i < (N as usize))
		// Fill in loop invariants here
	{
		c.set(i, 1);

		// Fill in a block of assertions here to complete the proof

		i = i + 1;
	}

	i = 0;
	while (i < (N as usize))
		// Fill in loop invariants here
	{
		let temp = sum[0] + a[i];
		sum.set(0, temp);

		// Fill in a block of assertions here to complete the proof

		i = i + 1;

		assert(sum[0] == i);
	}

	i = 0;
	while (i < (N as usize))
		// Fill in loop invariants here
	{
		let temp = sum[0] + b[i];
		sum.set(0, temp);

		// Fill in a block of assertions here to complete the proof

		i = i + 1;

		// Fill in a block of assertions here to complete the proof;
	}

	i = 0;
	while (i < (N as usize))
		// Fill in loop invariants here
	{
		let temp = sum[0] + c[i];
		sum.set(0, temp);

		// Fill in a block of assertions here to complete the proof

		i = i + 1;

		// Fill in a block of assertions here to complete the proof;
	}

	// Fill in a block of assertions here to complete the proof
}
}