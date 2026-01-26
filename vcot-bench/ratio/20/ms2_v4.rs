use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_mod2_is_0_or_1(i: usize)
    ensures
        i % 2 == 0 || i % 2 == 1,
{
    let r = i % 2;
    assert(r < 2) by {
        assert(2 > 0usize);
        assert(i % 2 < 2);
    };
    assert(r == 0 || r == 1) by {
        if r == 0 {
        } else {
            assert(r != 0);
            assert(r < 2);
            assert(r == 1);
        }
    };
}

// Complete the lemma function below
proof fn lemma_forall_extend_by_one_bit(a: &Vec<usize>, old_i: usize)
   

proof fn lemma_bit_is_0_or_1_implies_le_1(x: usize)
    requires
        x == 0 || x == 1,
    ensures
        x <= 1,
{
    if x == 0 {
        assert(x <= 1);
    } else {
        assert(x == 1);
        assert(x <= 1);
    }
}

proof fn lemma_sum0_update_bound(old_sum0: usize, bit: usize, i: usize)
    requires
        bit == 0 || bit == 1,
        old_sum0 <= i,
    ensures
        old_sum0 + bit <= i + 1,
{
    assert(old_sum0 + bit <= i + 1) by {
        if bit == 0 {
            assert(old_sum0 + bit == old_sum0);
            assert(old_sum0 <= i);
            assert(old_sum0 <= i + 1);
        } else {
            assert(bit == 1);
            assert(old_sum0 + bit == old_sum0 + 1);
            assert(old_sum0 + 1 <= i + 1) by {
                assert(old_sum0 <= i);
            };
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
	ensures
		sum[0] <= N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			forall |k:int| 0<= k < i ==> a[k] == 0 || a[k] == 1,
			a.len() == N,
	{
        assert(i < a.len());

        proof { lemma_mod2_is_0_or_1(i); }
        assert(i % 2 == 0 || i % 2 == 1);
        if i % 2 == 0 {
            // Fill in a block of assertions here to complete the proof;
        } else {
            assert(i % 2 == 1);
        };

        a.set(i, i % 2 );

        // Fill in a block of assertions here to complete the proof

        let old_i = i;
		i = i + 1;

        assert(forall |k:int| 0<= k < i ==> a[k] == 0 || a[k] == 1) by {
            assert(forall |k:int| 0<= k < old_i ==> a[k] == 0 || a[k] == 1);
            assert(a[(old_i as int)] == 0 || a[(old_i as int)] == 1);
            lemma_forall_extend_by_one_bit(&*a, old_i);
        };
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0<= k < N ==> a[k] == 0 || a[k] == 1,
			a.len() == N,
			sum.len() == 1,
			i>0 ==> sum[0] <= i,
	{
		if (i == 0) {
			sum.set(0, 0);
            // Fill in a block of assertions here to complete the proof;
		} else {
            assert(i > 0);

            assert(i < N);
            assert(i < a.len());

            assert(a[(i as int)] <= 1) by {
                lemma_bit_is_0_or_1_implies_le_1(a[(i as int)]);
            };

            assert(sum[0] <= i);

            let temp = sum[0] + a[i];

            assert(temp <= i + 1) by {
                lemma_sum0_update_bound(sum[0], a[(i as int)], i);
            };

			sum.set(0, temp);

            assert(sum[0] == temp);
		}
        let old_i = i;
		i = i + 1;

        assert(i <= N) by {
            assert(old_i < N);
            assert(old_i + 1 <= N);
        };

        assert(i > 0 ==> sum[0] <= i) by {
            if i > 0 {
                if old_i == 0 {
                    assert(i == 1);
                    // Fill in a block of assertions here to complete the proof;
                    assert(sum[0] <= i);
                } else {
                    assert(old_i > 0);
                    assert(i == old_i + 1);
                    assert(sum[0] <= i);
                }
            }
        };
	}

    assert(i == N);
    assert(sum[0] <= i);
    assert(sum[0] <= N);
}
}