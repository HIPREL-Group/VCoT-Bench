use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_i32_bounds_for_small_positive(n: i32)
   

// Complete the lemma function below
proof fn lemma_n_lt_1000_implies_n_plus_c_in_i32(n: i32, c: i32)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		forall |k:int| 0 <= k < N ==> b[k] == N + 2,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			forall |k:int| 0 <= k < i ==> a[k] == 1,
			a.len() == N,
	{
		let ghost pre = a@;
		assert((i as int) < pre.len()) by {
			assert(pre.len() == (N as int));
		}

		a.set(i, 1);

		let ghost post = a@;
		assert(post.len() == pre.len());
		assert(post.index(i as int) == 1i32);
		assert(forall |k:int| 0 <= k < i ==> post.index(k) == 1i32) by {
			assert(forall |k:int| 0 <= k < i ==> pre.index(k) == 1i32);
			assert forall |k:int| 0 <= k < i implies post.index(k) == 1i32 by {
				if k == (i as int) {
					assert(false);
				} else {
					assert(post.index(k) == pre.index(k));
				}
			}
		}

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0 <= k < N ==> a[k] == 1,
			a.len() == N,
			sum[0] == i,
			sum.len() == 1,
	{
		let temp = sum[0] + a[i];
		sum.set(0, temp);
		i = i + 1;

		assert(sum[0] == i);
	}

	i = 0;
	while (i < N as usize)
		invariant
			sum[0] == N,
			sum.len() == 1,
			forall |k:int| i <= k < N ==> a[k] == 1,
			forall |k:int| 0 <= k < i ==> a[k] == N + 1,
			a.len() == N,
			N < 1000,
	{
		let temp = a[i] + sum[0];
		assert(temp == 1 + N);

		let ghost pre = a@;
		assert((i as int) < pre.len()) by {
			assert(pre.len() == (N as int));
		}

		assert((-2147483648i32 as int) <= (temp as int) <= (2147483647i32 as int)) by {
			assert(temp == N + 1);
			lemma_n_lt_1000_implies_n_plus_c_in_i32(N, 1);
		}

		a.set(i, temp);
		let ghost post = a@;
		assert(post.len() == pre.len());
		assert(post.index(i as int) == temp);
		assert(a[(i as int)] == N + 1);

		assert(forall |k:int| 0 <= k < i ==> post.index(k) == (N + 1)) by {
			assert(forall |k:int| 0 <= k < i ==> pre.index(k) == (N + 1));
			assert forall |k:int| 0 <= k < i implies post.index(k) == (N + 1) by {
				if k == (i as int) {
					assert(false);
				} else {
					assert(post.index(k) == pre.index(k));
				}
			}
		}
		assert(forall |k:int| (i as int) < k < N ==> post.index(k) == 1) by {
			assert(forall |k:int| (i as int) < k < N ==> pre.index(k) == 1);
			assert forall |k:int| (i as int) < k < N implies post.index(k) == 1 by {
				if k == (i as int) {
					assert(false);
				} else {
					assert(post.index(k) == pre.index(k));
				}
			}
		}

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			forall |k:int| 0 <= k < N ==> a[k] == N + 1,
			a.len() == N,
			forall |k:int| 0 <= k < i ==> b[k] == N + 2,
			b.len() == N,
			N < 1000,
	{
		let temp = a[i];
		assert(temp + 1 == N + 2);

		let ghost pre_b = b@;
		assert((i as int) < pre_b.len()) by {
			assert(pre_b.len() == (N as int));
		}

		assert((-2147483648i32 as int) <= ((temp + 1) as int) <= (2147483647i32 as int)) by {
			assert(temp == N + 1);
			lemma_n_lt_1000_implies_n_plus_c_in_i32(N, 2);
		}

		b.set(i, temp + 1);

		let ghost post_b = b@;
		assert(post_b.len() == pre_b.len());
		assert(post_b.index(i as int) == (temp + 1));

		assert(b[(i as int)] == N + 2);

		i = i + 1;
	}
}
}