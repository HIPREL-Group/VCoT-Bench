use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_i32_bounds_for_small_positive(n: i32)
   

proof fn lemma_n_lt_1000_implies_n_plus_c_in_i32(n: i32, c: i32)
    requires
        0 < n,
        n < 1000,
        c == 1 || c == 2,
    ensures
        (-2147483648i32 as int) <= ((n + c) as int) <= (2147483647i32 as int),
{
    assert(0 <= n);
    assert(c == 1 || c == 2);
    assert(0 <= c);
    assert(0 <= n + c);
    assert(n + c < 2147483647) by {
        assert(n < 1000);
        if c == 1 {
            assert(n + c <= 1000);
        } else {
            assert(c == 2);
            assert(n + c <= 1001);
        }
        assert(1001 < 2147483647);
    }
    lemma_i32_bounds_for_small_positive((n + c) as i32);
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
		forall |k:int| 0 <= k < N ==> b[k] == N + 2,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		let ghost pre = a@;
		// Fill in a block of assertions here to complete the proof

		a.set(i, 1);

		let ghost post = a@;
		// Fill in a block of assertions here to complete the proof

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

		// Fill in a block of assertions here to complete the proof;
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		let temp = a[i] + sum[0];
		assert(temp == 1 + N);

		let ghost pre = a@;
		// Fill in a block of assertions here to complete the proof

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
		// Fill in loop invariants here
	{
		let temp = a[i];
		// Fill in a block of assertions here to complete the proof;

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
		// Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}
}
}