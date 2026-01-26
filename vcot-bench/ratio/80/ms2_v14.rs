use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_mod2_is_0_or_1(i: usize)
    

// Complete the lemma function below
proof fn lemma_forall_extend_by_one_bit(a: &Vec<usize>, old_i: usize)
   

// Complete the lemma function below
proof fn lemma_bit_is_0_or_1_implies_le_1(x: usize)
   

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
            assert(sum[0] == 0);
		} else {
            // Fill in a block of assertions here to complete the proof;

            let temp = sum[0] + a[i];

            // Fill in a block of assertions here to complete the proof;

			sum.set(0, temp);

            assert(sum[0] == temp);
		}
        let old_i = i;
		i = i + 1;

        // Fill in a block of assertions here to complete the proof;
	}

    // Fill in a block of assertions here to complete the proof;
}
}