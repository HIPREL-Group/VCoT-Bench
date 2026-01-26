use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_forall_set_singleton_push(
    a: &Vec<i32>,
    i: usize,
)
   

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

		assert(forall |k:int| 0<= k < i + 1 ==> a[k] == 1) by {
			lemma_forall_update_preserves_prefix_ones(&old_a, a, i);
		}

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

			assert(temp + 1 == 2);
			assert(a[(i as int)] == 2);
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
		invariant
			i <= N,
			a.len() == N,
			forall |k:int| 0<= k < N ==> a[k] == 2,
			sum.len() == 1,
			sum[0] == 2 * i,
			N < 1000,
	{
		if (a[i] == 2) {
            let old_sum = sum[0];

			let temp = sum[0] + a[i];
			assert(temp == sum[0] + 2);

			sum.set(0, temp);

            assert(sum[0] == 2 * (i + 1)) by {
                assert(sum[0] == temp);
            };
		} else {
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}

		i = i + 1;
	}
}
}