use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_mod2_is_0_or_1(i: usize)
    

proof fn lemma_forall_extend_by_one_bit(a: &Vec<usize>, old_i: usize)
    requires
        forall |k:int| 0 <= k < old_i ==> a[k] == 0 || a[k] == 1,
        a[(old_i as int)] == 0 || a[(old_i as int)] == 1,
    ensures
        forall |k:int| 0 <= k < old_i + 1 ==> a[k] == 0 || a[k] == 1,
{
    assert forall |k:int| 0 <= k < old_i + 1 implies a[k] == 0 || a[k] == 1 by {
        if k < (old_i as int) {
            assert(0 <= k < old_i);
            assert(a[k] == 0 || a[k] == 1);
        } else {
            assert(k >= (old_i as int));
            assert(k < old_i + 1);
            assert(k == (old_i as int)) by {
                assert(k - (old_i as int) == 0) by {
                    assert((old_i as int) <= k);
                    assert(k <= (old_i as int));
                };
            };
            assert(a[k] == 0 || a[k] == 1);
        }
    };
}

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

// Complete the lemma function below
proof fn lemma_sum0_update_bound(old_sum0: usize, bit: usize, i: usize)
   

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
		// Fill in loop invariants here
	{
        // Fill in a block of assertions here to complete the proof;
        if i % 2 == 0 {
            // Fill in a block of assertions here to complete the proof;
        } else {
            // Fill in a block of assertions here to complete the proof;
        };

        a.set(i, i % 2 );

        assert(i < a.len());

        assert(a[(i as int)] == i % 2);
        assert(a[(i as int)] == 0 || a[(i as int)] == 1) by {
            lemma_mod2_is_0_or_1(i);
        }

        let old_i = i;
		i = i + 1;

        // Fill in a block of assertions here to complete the proof;
	}

	i = 0;
	
	while (i < N as usize)
		// Fill in loop invariants here
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

            // Fill in a block of assertions here to complete the proof;

			sum.set(0, temp);

            // Fill in a block of assertions here to complete the proof;
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

    // Fill in a block of assertions here to complete the proof;
}
}