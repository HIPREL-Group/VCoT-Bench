use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_step_sum_bound(prev_sum: int, a_i: int, i: int)
    requires
        i > 0,
        prev_sum <= 3 * i,
        0 <= a_i,
        a_i <= 3,
    ensures
        prev_sum + a_i <= 3 * (i + 1)
{
    assert(prev_sum + a_i <= 3 * i + 3);
    assert(3 * i + 3 == 3 * (i + 1)) by (nonlinear_arith);
}

proof fn lemma_forall_extend_by_new_index_i32(a: &Vec<i32>, i: usize)
    requires
        i < a.len(),
        forall |k:int| 0 <= k < i ==> a[k] == k % 4,
        a[i as int] == (i as int) % 4,
    ensures
        forall |k:int| 0 <= k < i + 1 ==> a[k] == k % 4
{
    assert(forall |k:int| 0 <= k < i + 1 ==> a[k] == k % 4) by {
        assert_forall_by(|k:int| {
            requires(0 <= k < i + 1);
            ensures(a[k] == k % 4);
            if k < i {
                assert(a[k] == k % 4);
            } else {
                assert(k == i as int);
                assert(a[k] == a[i as int]);
                assert(a[i as int] == (i as int) % 4);
                assert(k % 4 == (i as int) % 4);
            }
        });
    };
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 3 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			forall |k:int| 0<= k < i ==> a[k] == k % 4,
			a.len() == N,
	{
		a.set(i, (i % 4) as i32);

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			i <= N,
			i>0 ==> sum[0] <= 3 * i,
			sum.len() == 1,
			forall |k:int| 0<= k < N ==> a[k] == k % 4,
			a.len() == N,
			N < 1000,
	{
		if (i == 0) {
			sum.set(0, 0);
			// Fill in a block of assertions here to complete the proof;
		} else {
			// Fill in a block of assertions here to complete the proof

			let temp = sum[0] + a[i];

			// Fill in a block of assertions here to complete the proof;

			sum.set(0, temp);

			// Fill in a block of assertions here to complete the proof;
		}

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;

		// Fill in a block of assertions here to complete the proof;
	}

	// Fill in a block of assertions here to complete the proof;

	if i > 0 {
		// Fill in a block of assertions here to complete the proof;
	}
	// Fill in a block of assertions here to complete the proof;
}
}