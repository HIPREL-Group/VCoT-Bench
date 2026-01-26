use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_forall_extend_one_more(a: &Vec<i32>, i: usize)
    requires
        a.len() > 0,
        i < a.len(),
        forall |k:int| 0 <= k < i as int ==> a[k] == 1,
        a[i as int] == 1,
    ensures
        forall |k:int| 0 <= k < (i + 1) as int ==> a[k] == 1
{
    assert forall |k:int| 0 <= k < (i + 1) as int implies a[k] == 1 by {
        if k < (i as int) {
            assert(a[k] == 1);
        } else {
            assert(k == (i as int));
            assert(a[k] == 1);
        }
    }
}

// Complete the lemma function below
proof fn lemma_forall_preserve_suffix_ones(a: &Vec<i32>, i: usize, N: usize)
   

// Complete the lemma function below
proof fn lemma_index_from_suffix_inv_is_one(a: &Vec<i32>, i: usize, N: usize)
   

proof fn lemma_index_from_all5_inv_is_5(a: &Vec<i32>, i: usize, N: usize)
    requires
        i < N,
        N <= a.len(),
        forall |k:int| 0 <= k < N as int ==> a[k] == 5,
    ensures
        a[i as int] == 5
{
    // Fill in a block of assertions here to complete the proof;
}

// Complete the lemma function below
proof fn lemma_update_sum_by_adding_five(sum_i: int, i: usize)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 5 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N)
		// Fill in loop invariants here
	{
		a.set(i, 1);

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	while (i < N)
		invariant
			forall |k:int| 0<= k < i ==> a[k] == 5,
			forall |k:int| i<= k < N ==> a[k] == 1,
			a.len() == N,
	{
		if (a[i] == 1) {
			let temp = a[i];
			// Fill in a block of assertions here to complete the proof

			a.set(i, temp + 4);
			// Fill in a block of assertions here to complete the proof;
		} else {
			let temp = a[i];
			assert(false) by {
				assert((i as int) <= (i as int));
				assert((i as int) < (N as int));
				assert(a[i as int] == 1);
				assert(a[(i as int)] == 1);
			};
			a.set(i, temp - 1);
		}

		// Fill in a block of assertions here to complete the proof;
        
		i = i + 1;
	}

	i = 0;
	while (i < N)
		// Fill in loop invariants here
	{
		// Fill in a block of assertions here to complete the proof

		if (a[i] == 5)
		{
			let temp = sum[0] + a[i];
            
            assert(sum[0] == 5 * (i as int));

			sum.set(0, temp);

			// Fill in a block of assertions here to complete the proof;
		} else {
			// Fill in a block of assertions here to complete the proof;
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}

		i = i + 1;
	}

	// Fill in a block of assertions here to complete the proof
}
}