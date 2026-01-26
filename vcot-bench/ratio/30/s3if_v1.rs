use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_forall_prefix_to_full(a: &Vec<i32>, i: int, n: int)
    requires
        a.len() == n,
        0 <= i <= n,
        forall |k:int| 0 <= k < i ==> a[k] == 3,
        forall |k:int| i <= k < n ==> a[k] == 3,
    ensures
        forall |k:int| 0 <= k < n ==> a[k] == 3,
{
    assert(forall |k:int| 0 <= k < n ==> a[k] == 3) by {
        assert forall |k:int| 0 <= k < n implies a[k] == 3 by {
            if k < i {
                assert(a[k] == 3);
            } else {
                assert(a[k] == 3);
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 3 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		// Fill in loop invariants here
	{
		a.set(i, 3);
		i = i + 1;
	}

	i = 0;

	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0<= k < N ==> a[k] == 3,
			a.len() == N,
			sum[0] == 3 * i,
			sum.len() == 1,
			N < 1000,
	{
		if (a[i] == 3) {
			let temp = sum[0] + a[i];
			sum.set(0, temp);
		} else {
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}

		i = i + 1;
	}
}
}