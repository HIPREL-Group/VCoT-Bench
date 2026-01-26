use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_forall_extend_one_more(a: &Vec<i32>, i: usize)
   

// Complete the lemma function below
proof fn lemma_forall_preserve_suffix_ones(a: &Vec<i32>, i: usize, N: usize)
   

proof fn lemma_index_from_suffix_inv_is_one(a: &Vec<i32>, i: usize, N: usize)
    requires
        i < N,
        N <= a.len(),
        forall |k:int| i as int <= k < N as int ==> a[k] == 1,
    ensures
        a[i as int] == 1
{
    assert(a[i as int] == 1);
}

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

proof fn lemma_update_sum_by_adding_five(sum_i: int, i: usize)
    requires
        sum_i == 5 * (i as int),
    ensures
        sum_i + 5 == 5 * ((i as int) + 1)
{
    assert(sum_i + 5 == 5 * (i as int) + 5);
    assert(5 * (i as int) + 5 == 5 * ((i as int) + 1)) by (nonlinear_arith);
}

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

		assert(forall |k:int| 0 <= k < i + 1 ==> a[k] == 1) by {
			assert(forall |k:int| 0 <= k < i ==> a[k] == 1);
			assert(a[i as int] == 1);
			lemma_forall_extend_one_more(a, i);
		};

		i = i + 1;
	}

	i = 0;
	while (i < N)
		// Fill in loop invariants here
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
            
            // Fill in a block of assertions here to complete the proof;

			sum.set(0, temp);

			assert(sum[0] == 5 * ((i as int) + 1)) by {
				assert(sum[0] == (5 * (i as int)) + 5);
				lemma_update_sum_by_adding_five(5 * (i as int), i);
			};
		} else {
			assert(false) by {
				assert(a[(i as int)] == 5);
			};
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}

		i = i + 1;
	}

	// Fill in a block of assertions here to complete the proof
}
}