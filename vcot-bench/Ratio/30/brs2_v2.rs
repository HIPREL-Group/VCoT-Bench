use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_a_elem_bound(a: &Vec<i32>, k: int)
    requires
        0 <= k < a.len(),
        a[k] == 2 || a[k] == 0,
    ensures
        0 <= a[k] as int <= 2,
{
    if a[k] == 2 {
        assert(a[k] as int == 2);
        assert(0 <= a[k] as int);
        assert(a[k] as int <= 2);
    } else {
        assert(a[k] == 0);
        assert(a[k] as int == 0);
        assert(0 <= a[k] as int);
        assert(a[k] as int <= 2);
    }
}

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
		// Fill in loop invariants here
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
		invariant
			i <= N,
			forall |k:int| 0<= k < N ==> a[k] == 2 || a[k] == 0,
			a.len() == N,
			sum.len() == 1,
			i > 0 ==> sum[0] <= 2 * i,
			N < 1000,
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			let temp = sum[0];

            proof {
			    assert(a[i as int] == 2 || a[i as int] == 0);
			    lemma_a_elem_bound(a, (i as int));
            }

			assert(i > 0);
			assert(sum[0] <= 2 * (i as int));

			sum.set(0, temp + a[i]);
		}
		i = i + 1;
	}

	// Fill in a block of assertions here to complete the proof;
	if i > 0 {
		assert(sum[0] <= 2 * (i as int));
	}
}
}