use vstd::prelude::*;
fn main() {}
verus!{

pub proof fn lemma_forall_extend_one<T>(i: int, f: spec_fn(int) -> T, v: T)
    requires
        forall |j: int| 0 <= j < i ==> #[trigger] f(j) == v,
    ensures
        forall |j: int| 0 <= j < i + 1 ==> (if j == i { v } else { #[trigger] f(j) }) == v,
{
    assert(forall |j: int| 0 <= j < i + 1 ==> (if j == i { v } else { #[trigger] f(j) }) == v) by {
        assert forall |j: int| 0 <= j < i + 1 implies (if j == i { v } else { #[trigger] f(j) }) == v by {
            if j == i {
            } else {
                assert(f(j) == v);
            }
        }
    }
}

proof fn lemma_vec_set_extends_ones(v: &Vec<i32>, i: usize)
    requires
        i < v.len(),
        forall |j: int| 0 <= j < i ==> v[j] == 1,
    ensures
        forall |j: int| 0 <= j < i + 1 ==> (if j == (i as int) { 1 } else { v[j] }) == 1,
{
    lemma_forall_extend_one::<i32>((i as int), |j: int| v[j], 1);
}

proof fn lemma_vec_set_extends_ones_after_set(v: &Vec<i32>, i: usize)
    requires
        i < v.len(),
        v[(i as int)] == 1,
        forall |j: int| 0 <= j < i ==> v[j] == 1,
    ensures
        forall |j: int| 0 <= j < i + 1 ==> v[j] == 1,
{
    assert forall |j: int| 0 <= j < i + 1 implies v[j] == 1 by {
        if j == (i as int) {
        } else {
            assert(v[j] == 1);
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(c).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] <= 3 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < (N as usize))
		// Fill in loop invariants here
	{
		a.set(i, 1);

		assert(forall |j: int| 0 <= j < i + 1 ==> a[j] == 1) by {
			assert forall |j: int| 0 <= j < i + 1 implies a[j] == 1 by {
				if j == (i as int) {
				} else {
					assert(a[j] == 1);
				}
			}
		}

		i = i + 1;
	}

	i = 0;
	while (i < (N as usize))
		// Fill in loop invariants here
	{
		b.set(i, 1);

		assert(forall |j: int| 0 <= j < i + 1 ==> b[j] == 1) by {
			assert forall |j: int| 0 <= j < i + 1 implies b[j] == 1 by {
				if j == (i as int) {
				} else {
					assert(b[j] == 1);
				}
			}
		}

		i = i + 1;
	}

	i = 0;
	while (i < (N as usize))
		// Fill in loop invariants here
	{
		c.set(i, 1);

		assert(forall |j: int| 0 <= j < i + 1 ==> c[j] == 1) by {
			assert forall |j: int| 0 <= j < i + 1 implies c[j] == 1 by {
				if j == (i as int) {
				} else {
					assert(c[j] == 1);
				}
			}
		}

		i = i + 1;
	}

	i = 0;
	while (i < (N as usize))
		// Fill in loop invariants here
	{
		let temp = sum[0] + a[i];
		sum.set(0, temp);

		assert(sum[0] == (i as i32) + 1) by {
			let s_before: int = temp - a[(i as int)];
			assert(temp == s_before + a[(i as int)]);
			assert(a[(i as int)] == 1);
			assert(temp == s_before + 1);
			assert(sum[0] == temp);
			assert(s_before == (i as i32));
		}

		i = i + 1;

		assert(sum[0] == i);
	}

	i = 0;
	while (i < (N as usize))
		// Fill in loop invariants here
	{
		let temp = sum[0] + b[i];
		sum.set(0, temp);

		assert(sum[0] == (i as i32) + N + 1) by {
			let s_before: int = temp - b[(i as int)];
			assert(temp == s_before + b[(i as int)]);
			assert(b[(i as int)] == 1);
			assert(temp == s_before + 1);
			assert(s_before == (i as i32) + N);
		}

		i = i + 1;

		assert(sum[0] == i + N);
	}

	i = 0;
	while (i < (N as usize))
		// Fill in loop invariants here
	{
		let temp = sum[0] + c[i];
		sum.set(0, temp);

		assert(sum[0] == (i as i32) + 2 * N + 1) by {
			let s_before: int = temp - c[(i as int)];
			assert(temp == s_before + c[(i as int)]);
			assert(c[(i as int)] == 1);
			assert(temp == s_before + 1);
			assert(s_before == (i as i32) + 2 * N);
		}

		i = i + 1;

		assert(sum[0] == i + 2 * N);
	}

	assert(sum[0] <= 3 * N) by {
		assert(sum[0] == 3 * N);
	}
}
}