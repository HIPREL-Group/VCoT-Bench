use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
pub proof fn lemma_forall_extend_one<T>(i: int, f: spec_fn(int) -> T, v: T)
   

proof fn lemma_vec_set_extends_ones(v: &Vec<i32>, i: usize)
    requires
        i < v.len(),
        forall |j: int| 0 <= j < i ==> v[j] == 1,
    ensures
        forall |j: int| 0 <= j < i + 1 ==> (if j == (i as int) { 1 } else { v[j] }) == 1,
{
    lemma_forall_extend_one::<i32>((i as int), |j: int| v[j], 1);
}

proof fn lemma_vec_set_extends_ones_after_set(v: &Vec<i32>, i: usize)
    requires
        i < v.len(),
        v[(i as int)] == 1,
        forall |j: int| 0 <= j < i ==> v[j] == 1,
    ensures
        forall |j: int| 0 <= j < i + 1 ==> v[j] == 1,
{
    assert forall |j: int| 0 <= j < i + 1 implies v[j] == 1 by {
        if j == (i as int) {
        } else {
            assert(v[j] == 1);
        }
    }
}

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

		assert(forall |j: int| 0 <= j < i + 1 ==> a[j] == 1) by {
			assert forall |j: int| 0 <= j < i + 1 implies a[j] == 1 by {
				if j == (i as int) {
				} else {
					assert(a[j] == 1);
				}
			}
		}

		i = i + 1;
	}

	i = 0;
	while (i < (N as usize))
		invariant
			forall |j: int| 0<= j < i ==> b[j] == 1,
			b.len() == N,
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

		// Fill in a block of assertions here to complete the proof;
	}

	i = 0;
	while (i < (N as usize))
		invariant
			i <= N,
			sum.len() == 1,
			sum[0] == i + N,
			forall |j: int| 0<= j < N ==> b[j] == 1,
			b.len() == N,
			N < 1000,
	{
		let temp = sum[0] + b[i];
		sum.set(0, temp);

		// Fill in a block of assertions here to complete the proof

		i = i + 1;

		// Fill in a block of assertions here to complete the proof;
	}

	i = 0;
	while (i < (N as usize))
		invariant
			i <= N,
			sum.len() == 1,
			sum[0] == i + 2 * N,
			forall |j: int| 0<= j < N ==> c[j] == 1,
			c.len() == N,
			N < 1000,
	{
		let temp = sum[0] + c[i];
		sum.set(0, temp);

		// Fill in a block of assertions here to complete the proof

		i = i + 1;

		assert(sum[0] == i + 2 * N);
	}

	// Fill in a block of assertions here to complete the proof
}
}