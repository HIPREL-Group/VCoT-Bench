use vstd::prelude::*;
fn main() {}

verus!{

// Complete the lemma function below
proof fn lemma_inner_step_preserves_bounds(i: int, j: int, ai: int)
   

// Complete the lemma function below
proof fn lemma_outer_sum_step(sum: int, ai: int, i: int)
   

proof fn lemma_i32_add_bounds_preserved_for_small(n: int)
    requires
        n <= 0x3FFF_FFFF,
        0 <= n,
    ensures
        2*n <= i32::MAX as int,
        0 <= n,
{
    assert(0 <= n);
    assert(2*n <= i32::MAX as int);
}

#[verifier::exec_allows_no_decreases_clause]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2*N
{  
    let mut i: usize = 0;
    let mut sum: i32 = 0;

    proof {
        lemma_i32_add_bounds_preserved_for_small((N as int));
    }

    while (i < N as usize) 
        // Fill in loop invariants here
    {  
        a.set(i, b[i] + 1);

        proof {
            assert(0 <= (i as int) < b.len());
            assert((i as int) <= (b[(i as int)] as int) <= (i as int) + 1);

            assert((i as int) + 1 <= ((b[(i as int)] + 1) as int) <= (i as int) + 2);
        }

        let mut j: usize = 0;
        while (j < i)
            // Fill in loop invariants here
        {
            let temp = a[i];

            // Fill in a block of assertions here to complete the proof

            a.set(i, temp - 1);

            j = j + 1;
        }

        // Fill in a block of assertions here to complete the proof

        sum = sum + a[i];

        // Fill in a block of assertions here to complete the proof

        i = i + 1;
    }  

    proof {
        assert((N as int) <= (sum as int) <= 2*(N as int));
    }

    sum
}
}