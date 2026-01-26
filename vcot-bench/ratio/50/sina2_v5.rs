use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_vec_set_updates_view_at_i32(v: Seq<i32>, i: int, val: i32)
    requires
        0 <= i < v.len(),
    ensures
        v.update(i, val).len() == v.len(),
{
}

proof fn lemma_vec_set_gives_value_i32(v: Seq<i32>, i: int, val: i32)
    requires
        0 <= i < v.len(),
    ensures
        v.update(i, val)[i] == val,
{
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			forall |k:int| 0 <= k < i ==> a[k] == 1,
			a.len() == N,
	{
		a.set(i, 1);

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		let temp = sum[0] + a[i];

		assert(temp == i + 1) by {
			assert(a[i as int] == 1);
		};

		sum.set(0, temp);

		assert(sum[0] == i + 1) by {
			assert(temp == i + 1);
		};

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			sum[0] == N,
			forall |k:int| 0 <= k < i ==> a[k] == N + 1,
			forall |k:int| i <= k < N ==> a[k] == 1,
			a.len() == N,
			sum.len() == 1,
			N < 1000,
	{
		let temp = a[i] + sum[0];

		// Fill in a block of assertions here to complete the proof;

		a.set(i, temp);

        // Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	// Fill in a block of assertions here to complete the proof;
}
}