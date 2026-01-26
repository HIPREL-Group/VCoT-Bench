use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_forall_prefix_update_to_1(old_a: Seq<i32>, new_a: Seq<i32>, idx: int, old_i: int)
    requires
        0 <= idx < old_a.len(),
        idx == old_i,
        new_a == old_a.update(idx, 1),
        forall |j: int| 0 <= j < old_i ==> old_a[j] == 1,
    ensures
        forall |j: int| 0 <= j < old_i + 1 ==> new_a[j] == 1,
{
    assert forall |j: int| 0 <= j < old_i + 1 implies new_a[j] == 1 by {
        if j == idx {
            assert(new_a[j] == 1) by {
                assert(new_a == old_a.update(idx, 1));
            };
        } else {
            assert(0 <= j < old_i) by {
                assert(0 <= j);
                assert(j < old_i + 1);
                assert(j != old_i);
                assert(j < old_i);
            };
            assert(new_a[j] == old_a[j]) by {
                assert(new_a == old_a.update(idx, 1));
            };
            assert(old_a[j] == 1) by {
                assert(0 <= j < old_i);
            };
            assert(new_a[j] == 1);
        }
    };
}

proof fn lemma_forall_prefix_update_to_5(old_a: Seq<i32>, new_a: Seq<i32>, idx: int, old_i: int)
    requires
        0 <= idx < old_a.len(),
        idx == old_i,
        new_a == old_a.update(idx, 5),
        forall |j: int| 0 <= j < old_i ==> old_a[j] == 5,
    ensures
        forall |j: int| 0 <= j < old_i + 1 ==> new_a[j] == 5,
{
    assert forall |j: int| 0 <= j < old_i + 1 implies new_a[j] == 5 by {
        if j == idx {
            assert(new_a[j] == 5) by {
                assert(new_a == old_a.update(idx, 5));
            };
        } else {
            assert(0 <= j < old_i) by {
                assert(0 <= j);
                assert(j < old_i + 1);
                assert(j != old_i);
                assert(j < old_i);
            };
            assert(new_a[j] == old_a[j]) by {
                assert(new_a == old_a.update(idx, 5));
            };
            assert(old_a[j] == 5) by {
                assert(0 <= j < old_i);
            };
            assert(new_a[j] == 5);
        }
    };
}

proof fn lemma_forall_suffix_shrink(old_a: Seq<i32>, i0: int, n: int)
    requires
        forall |j: int| i0 <= j < n ==> old_a[j] == 1,
    ensures
        forall |j: int| i0 + 1 <= j < n ==> old_a[j] == 1,
{
    assert forall |j: int| i0 + 1 <= j < n implies old_a[j] == 1 by {
        assert(i0 <= j) by {
            assert(i0 + 1 <= j);
        };
        assert(old_a[j] == 1) by {
            assert(i0 <= j < n);
        };
    };
}

// Complete the lemma function below
proof fn lemma_update_preserves_suffix_except_at_idx(old_a: Seq<i32>, idx: int, n: int)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 5 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			a.len() == N,
			forall |j: int| 0<= j < i ==> a[j] == 1,
	{
		a.set(i, 1);

		let ghost old_i: int = i as int;
		let ghost old_view = a@;

		i = i + 1;

		assert(forall |j: int| 0 <= j < i ==> a[j] == 1) by {
			let prev_i: int = (i as int) - 1;
			assert(prev_i == old_i);

			assert(a[prev_i] == 1) by {
				assert(a@ == old_view.update(old_i, 1));
			};

			lemma_forall_prefix_update_to_1(old_view, a@, old_i, old_i);
		};
	}

	i = 0;
	while (i < N as usize)
		invariant
			a.len() == N,
			forall |j: int| 0<= j < i ==> a[j] == 5,
			forall |j: int| i <= j < N ==> a[j] == 1,
	{
		let ghost old_i: int = i as int;
		let ghost old_view = a@;

		if (a[i] == 1) {
			let temp = a[i];

			a.set(i, temp + 4);

			assert(a[(i as int)] == 5) by {
				assert(a@ == old_view.update(old_i, 5));
			};
		} else {
			let temp = a[i];
			assert(false) by {
				assert(a[(i as int)] == 1);
				assert(a[(i as int)] != 1);
			};
			a.set(i, temp - 1);
		}

		i = i + 1;

		assert(forall |j: int| 0 <= j < i ==> a[j] == 5) by {
			lemma_forall_prefix_update_to_5(old_view, a@, old_i, old_i);
		};
		assert(forall |j: int| i <= j < N ==> a[j] == 1) by {
			lemma_forall_suffix_shrink(old_view, old_i, (N as int));
			lemma_update_preserves_suffix_except_at_idx(old_view, old_i, (N as int));

			assert forall |j: int| (i as int) <= j < N implies a[j] == 1 by {
				assert((i as int) == old_i + 1);
				assert(old_i + 1 <= j < N);
				if j == old_i {
					assert(false) by { assert(old_i + 1 <= j); }
				} else {
					assert(a@ == old_view.update(old_i, 5));
					assert(a[j] == old_view.update(old_i, 5)[j]);
					assert(old_view.update(old_i, 5)[j] == old_view[j]);
					assert(old_view[j] == 1) by {
						assert(old_i + 1 <= j < N);
					};
					assert(a[j] == 1);
				}
			};
		};
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			a.len() == N,
			sum.len() == 1,
			forall |j: int| 0<= j < N ==> a[j] == 5,
			sum[0] == 5 * i,
			N < 1000,
	{
		let ghost old_i: int = i as int;

		let temp = sum[0] + a[i];

		assert(temp == 5 * (i + 1)) by {
			assert(sum[0] == 5 * i);
			assert(a[(i as int)] == 5);
		};

		sum.set(0, temp);

		i = i + 1;

		assert(sum[0] == 5 * i) by {
			assert((sum[0] as int) == 5 * (old_i + 1)) by {
				assert(temp == 5 * (old_i + 1));
			};
		};
	}

	assert(sum[0] == 5 * N) by {
		assert(i == N as usize);
	};
}
}