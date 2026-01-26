use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_seq_update_extends_forall_prefix_1(old_s: Seq<i32>, new_s: Seq<i32>, i0: int)
    requires
        0 <= i0,
        new_s == old_s.update(i0, 1),
        forall |k:int| 0 <= k < i0 ==> old_s[k] == 1,
        i0 < old_s.len(),
    ensures
        forall |k:int| 0 <= k < i0 + 1 ==> new_s[k] == 1,
{
    assert forall |k:int| 0 <= k < i0 + 1 implies new_s[k] == 1 by {
        if k < i0 {
            assert(old_s[k] == 1);

            assert(k != i0);
            assert(new_s[k] == old_s[k]);
        } else {
            assert(k == i0);
            assert(new_s[i0] == 1);
        }
    }
}

proof fn lemma_vec_set_view_update_i32(v: &Vec<i32>, i: usize, val: i32)
    requires
        i < v.len(),
    ensures
        true,
{
}

// Complete the lemma function below
proof fn lemma_second_loop_if_branch_sets_i_to_6(a: &Vec<i32>, i: usize)
   

proof fn lemma_second_loop_else_branch_sets_i_to_5(a: &Vec<i32>, i: usize)
    requires
        i < a.len(),
        a[(i as int)] == 6,
    ensures
        a@.update((i as int), (a[(i as int)] - 1) as i32)[(i as int)] == 5,
{
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 6 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N)
		invariant
			forall |k:int| 0 <= k < i ==> a[k] == 1,
			a.len() == N,
	{
		let old_view = Ghost(a@);
		a.set(i, 1);

        assert(a@ == old_view@.update((i as int), 1)) by {
            lemma_vec_set_view_update_i32(a, i, 1);
        };

		i = i + 1;

        assert(forall |k:int| 0 <= k < i ==> a[k] == 1) by {
            let i0: int = (i - 1) as int;

            assert(i0 < old_view@.len()) by {
                assert(old_view@.len() == a@.len());
                assert(a@.len() == (N as int));
                assert(i0 < (i as int));
                assert((i as int) <= (N as int));
            }

            lemma_seq_update_extends_forall_prefix_1(old_view@, a@, i0);

            assert forall |k:int| 0 <= k < i implies a[k] == 1 by {
                assert(0 <= k < (i as int));
                assert(0 <= k < i0 + 1);
                assert(a@[k] == 1);
            }
        }
	}

	i = 0;
	while (i < N)
		invariant
			forall |k:int| 0 <= k < i ==> a[k] == 6,
			forall |k:int| i <= k < N ==> a[k] == 1,
			a.len() == N,
	{
		if (a[i] == 1) {
			let temp = a[i];
            proof {
			    lemma_second_loop_if_branch_sets_i_to_6(a, i);
            }
			a.set(i, temp + 5);
		} else {
			let temp = a[i];
            proof {
			    lemma_second_loop_else_branch_sets_i_to_5(a, i);
            }
			a.set(i, temp - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N)
		invariant
			i <= N,
			forall |k:int| 0 <= k < N ==> a[k] == 6,
			a.len() == N,
			sum[0] == 6 * i,
			sum.len() == 1,
			N < 1000,
	{
		assert(a[(i as int)] == 6);

		if (a[i] == 6)
		{
			let temp = sum[0] + a[i];
			sum.set(0, temp);
			assert(sum[0] == 6 * (i + 1)) by {
				assert(6 * (i + 1) == 6 * i + 6);
			}
		} else {
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}
		i = i + 1;

		assert(sum[0] == 6 * i);
	}

	assert(sum[0] == 6 * N);
}
}