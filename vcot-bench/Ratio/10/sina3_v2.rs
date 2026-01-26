use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_forall_range_extend_one(
    a: &Vec<i32>,
    i: usize,
)
    requires
        forall |k:int| 0 <= k < i ==> a[k] == 1,
        i < a.len(),
        a[(i as int)] == 1,
    ensures
        forall |k:int| 0 <= k < i + 1 ==> a[k] == 1,
{
    assert forall |k:int| 0 <= k < i + 1 implies a[k] == 1 by {
        if k < i {
            assert(a[k] == 1);
        } else {
            assert(k == i) by {
                assert(0 <= k < i + 1);
                assert(!(k < i));
            };
            assert(a[(i as int)] == 1);
        }
    }
}

proof fn lemma_forall_range_extend_one_b(
    b: &Vec<i32>,
    i: usize,
)
    requires
        forall |k:int| 0 <= k < i ==> b[k] == 1,
        i < b.len(),
        b[(i as int)] == 1,
    ensures
        forall |k:int| 0 <= k < i + 1 ==> b[k] == 1,
{
    assert forall |k:int| 0 <= k < i + 1 implies b[k] == 1 by {
        if k < i {
            assert(b[k] == 1);
        } else {
            assert(k == i) by {
                assert(0 <= k < i + 1);
                assert(!(k < i));
            }
            assert(b[(i as int)] == 1);
        }
    }
}

proof fn lemma_sum_loop_step(
    sum: &Vec<i32>,
    a: &Vec<i32>,
    i: usize,
)
    requires
        sum.len() == 1,
        a.len() > i,
        forall |k:int| 0 <= k < a.len() ==> a[k] == 1,
        sum[0] == (i as int),
    ensures
        sum[0] + a[(i as int)] == (i as int) + 1,
{
    assert(a[(i as int)] == 1);
}

proof fn lemma_last_loop_step_sets_n_plus_1(
    a: &Vec<i32>,
    b: &Vec<i32>,
    sum: &Vec<i32>,
    i: usize,
    N: i32,
)
    requires
        b.len() == N,
        a.len() == N,
        sum.len() == 1,
        sum[0] == N,
        forall |k:int| 0 <= k < N ==> b[k] == 1,
        i < N as usize,
        a[(i as int)] == 1,
        b[(i as int)] == 1,
    ensures
        b[(i as int)] + sum[0] == N + 1,
{
}

// Complete the lemma function below
proof fn lemma_index_in_forall_i32_range_implies_eq_1(
    v: &Vec<i32>,
    N: i32,
    i: usize,
)
   

proof fn lemma_update_preserves_prefix_property(
    v: &Vec<i32>,
    i: usize,
)
    requires
        forall |k:int| 0 <= k < i ==> v[k] == 1,
        v[(i as int)] == 1,
        i < v.len(),
    ensures
        forall |k:int| 0 <= k < i + 1 ==> v[k] == 1,
{
    lemma_forall_range_extend_one(v, i);
}

proof fn lemma_update_preserves_prefix_property_b(
    v: &Vec<i32>,
    i: usize,
)
    requires
        forall |k:int| 0 <= k < i ==> v[k] == 1,
        v[(i as int)] == 1,
        i < v.len(),
    ensures
        forall |k:int| 0 <= k < i + 1 ==> v[k] == 1,
{
    lemma_forall_range_extend_one_b(v, i);
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			forall |k:int| 0 <= k < i ==> a[k] == 1,
			a.len() == N,
	{
		a.set(i, 1);

        proof {
            lemma_update_preserves_prefix_property(a, i);
        }

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			forall |k:int| 0 <= k < i ==> b[k] == 1,
			b.len() == N,
	{
		b.set(i, 1);

        proof {
            lemma_update_preserves_prefix_property_b(b, i);
        }

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			sum.len() == 1,
			forall |k:int| 0 <= k < N ==> a[k] == 1,
			a.len() == N,
			sum[0] == i,
	{
        proof {
            lemma_sum_loop_step(sum, a, i);
        }

		let temp = sum[0] + a[i];
		sum.set(0, temp);

        proof {
            assert(sum[0] == i + 1) by {
                assert(sum[0] == temp);
                assert(temp == sum@[0]) by { };
                assert(sum@[0] == (i as int) + 1) by {
                    assert(sum@[0] == (sum@[0] + a[(i as int)]) - a[(i as int)]) by { };
                }
            }
        }

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
        proof {
            lemma_last_loop_step_sets_n_plus_1(a, b, sum, i, N);
        }

		let temp = b[i] + sum[0];
		a.set(i, temp);

        proof {
            assert(a[(i as int)] == N + 1) by {
                assert(a[(i as int)] == temp);
                assert(temp == b[(i as int)] + sum[0]);
                assert(b[(i as int)] + sum[0] == N + 1);
            }
        }

		i = i + 1;
	}
}
}