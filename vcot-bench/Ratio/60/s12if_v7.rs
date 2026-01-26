use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_forall_set_singleton_push(
    a: &Vec<i32>,
    i: usize,
)
    requires
        a.len() > 0,
        i < a.len(),
        forall |k:int| 0 <= k < i ==> a[k] == 1,
        a[(i as int)] == 1,
    ensures
        forall |k:int| 0 <= k < i + 1 ==> (if k < i { a[k] == 1 } else { k == (i as int) ==> a[k] == 1 }),
{
    assert forall |k:int| 0 <= k < i + 1 implies (if k < i { a[k] == 1 } else { k == (i as int) ==> a[k] == 1 }) by {
        if 0 <= k < i + 1 {
            if k < (i as int) {
                assert(a[k] == 1) by {
                    assert(0 <= k < (i as int));
                }
            } else {
                if k == (i as int) {
                    assert(k == (i as int) ==> a[k] == 1) by {
                        if k == (i as int) {}
                    }
                } else {
                    assert(k == (i as int) ==> a[k] == 1) by {
                        if k == (i as int) {}
                    }
                }
            }
        }
    }
}

// Complete the lemma function below
proof fn lemma_forall_update_preserves_prefix_ones(
    a_before: &Vec<i32>,
    a_after: &Vec<i32>,
    i: usize,
)
   

// Complete the lemma function below
proof fn lemma_forall_update_preserves_prefix_twos(
    a_before: &Vec<i32>,
    a_after: &Vec<i32>,
    i: usize,
)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 2 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N)
		invariant
			a.len() == N,
			forall |k:int| 0<= k < i ==> a[k] == 1,
	{
		let ghost old_a = *a;

		a.set(i, 1);

		// Fill in a block of assertions here to complete the proof

		i = i + 1;
	}

	i = 0;
	while (i < N)
		invariant
			a.len() == N,
			forall |k:int| 0<= k < i ==> a[k] == 2,
			forall |k:int| i<= k < N ==> a[k] == 1,
	{
		let ghost old_a = *a;

		if (a[i] == 1) {
			let temp = a[i];
			a.set(i, temp + 1);

			// Fill in a block of assertions here to complete the proof;
		} else {
			let temp = a[i];
			a.set(i, temp - 1);
		}

		assert(forall |k:int| 0<= k < i + 1 ==> a[k] == 2) by {
			lemma_forall_update_preserves_prefix_twos(&old_a, a, i);
		}

		i = i + 1;
	}

	i = 0;
	while (i < N)
		// Fill in loop invariants here
	{
		if (a[i] == 2) {
            let old_sum = sum[0];

			let temp = sum[0] + a[i];
			// Fill in a block of assertions here to complete the proof;

			sum.set(0, temp);

            // Fill in a block of assertions here to complete the proof;
		} else {
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}

		i = i + 1;
	}
}
}