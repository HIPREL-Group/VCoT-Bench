use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_vec_set_invariant_0_or_5(
    a_before: &Vec<i32>,
    a_after: &Vec<i32>,
    i: usize,
    v: i32,
)
    requires
        a_before.len() == a_after.len(),
        i < a_before.len(),
        v == 0 || v == 5,
        forall |k:int| 0 <= k < i as int ==> a_before[k] == 0 || a_before[k] == 5,
        a_after@ == a_before@.update(i as int, v),
    ensures
        forall |k:int| 0 <= k < (i + 1) as int ==> a_after[k] == 0 || a_after[k] == 5,
{
    assert forall |k:int| 0 <= k < (i + 1) as int implies a_after[k] == 0 || a_after[k] == 5 by {
        if k < i as int {
            assert(a_before[k] == 0 || a_before[k] == 5);
            assert(a_after[k] == a_before[k]);
        } else {
            assert(k == i as int);
            assert(a_after[k] == v);
        }
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
		sum[0] <= 5 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		if (i % 5 == 0) {
			a.set(i, 5);
		} else {
			a.set(i, 0);
		}

        assert forall |k:int| 0 <= k < (i + 1) implies a[k] == 5 || a[k] == 0 by {
            if k < i as int {
                assert(a[k] == 5 || a[k] == 0);
            } else {
                assert(a[k] == 5 || a[k] == 0);
            }
        };

		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0<= k < N ==> a[k] == 5 || a[k] == 0,
			a.len() == N,
			sum.len() == 1,
			i>0 ==> sum[0] <= 5 * i,
			N < 1000,
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
            let ai: i32 = a[i];
            let temp = sum[0];

			sum.set(0, temp + a[i]);

            // Fill in a block of assertions here to complete the proof
		}

		i = i + 1;
	}

    // Fill in a block of assertions here to complete the proof;
}
}