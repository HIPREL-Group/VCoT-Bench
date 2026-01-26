use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_set_preserves_prefix_ones(a: &Vec<i32>, i: usize)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	ensures
		sum[0] == N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			forall |k:int| 0<= k < i ==> a[k] == 1,
			a.len() == N,
	{
		assert(i < a.len()) by {
            assert(a.len() == N);
        };
		assert(a.len() == N);

		proof {
			lemma_set_preserves_prefix_ones(a, i);
		}

		a.set(i, 1);

		assert(forall |k:int| 0 <= k < i + 1 ==> a[k] == 1);

		i = i + 1;

		assert(forall |k:int| 0<= k < i ==> a[k] == 1);
		assert(a.len() == N);
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0<= k < N ==> a[k] == 1,
			a.len() == N,
			sum[0] == i,
			sum.len() == 1,
	{
		assert(i < a.len()) by {
            assert(a.len() == N);
        };
		assert(a.len() == N);

		assert(a[i as int] == 1) by {
			assert(forall |k:int| 0 <= k < N ==> a[k] == 1);
			assert(a[i as int] == 1);
		};

		if (a[i] == 1) {
			let temp = sum[0] + a[i];
			assert(temp == i as i32 + 1) by {
				assert(sum[0] as int == i as int);
				assert(a[i as int] as int == 1);
				assert(temp as int == sum[0] as int + a[i as int] as int);
				assert(temp as int == i as int + 1);
			};

			sum.set(0, temp);

			assert(sum[0] == i as i32 + 1);
		} else {
			assert(false) by {
				assert(a[i as int] == 1);
			};
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}

		i = i + 1;

		assert(sum[0] == i) by {
            assert(sum[0] as int == (i as int));
        };
	}

	assert(sum[0] == N) by {
        assert(!(i < N as usize));
        assert(i <= N);
        assert(i == N as usize) by {
            if i < N as usize {
                assert(false);
            } else {
                assert(i >= N as usize);
                assert(i <= N as usize) by {
                    assert(i <= N);
                };
            }
        };
        assert(sum[0] == i);
        assert(sum[0] == N) by {
            assert(i == N as usize);
        };
	};
}
}