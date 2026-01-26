use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 4 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			forall |k:int| 0<= k < i ==> a[k] == 4 || a[k] == 0,
			a.len() == N,
	{
		if (i % 4 == 0) {
			a.set(i, 4);
		} else {
			a.set(i, 0);
		}

        assert(forall |k:int| 0 <= k < i + 1 ==> a[k] == 4 || a[k] == 0) by {
            assert(forall |k:int| 0 <= k < i ==> a[k] == 4 || a[k] == 0);
            assert(a[i as int] == 4 || a[i as int] == 0);
        }

		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0<= k < N ==> a[k] == 4 || a[k] == 0,
			a.len() == N,
			sum.len() == 1,
			i > 0 ==> sum[0] <= 4 * i,
			N < 1000,
	{
		if (i == 0) {
			sum.set(0, 0);
            assert(sum[0] <= 4 * (i + 1)) by {
                assert(sum[0] == 0);
            }
		} else {
            assert(a[i as int] == 4 || a[i as int] == 0);

            let temp = sum[0];

            if a[i] == 4 {
                sum.set(0, temp + 4);
            } else {
                sum.set(0, temp + 0);
            }

            // Fill in a block of assertions here to complete the proof
		}
		i = i + 1;
	}

    // Fill in a block of assertions here to complete the proof
}
}