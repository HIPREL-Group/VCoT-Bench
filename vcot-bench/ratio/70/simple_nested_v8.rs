use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_inner_step_preserves_bounds(i: int, j: int, ai: int)
    requires
        0 <= j < i,
        i + 1 - j <= ai <= i + 2 - j,
    ensures
        i + 1 - (j + 1) <= ai - 1 <= i + 2 - (j + 1),
{
}

proof fn lemma_outer_sum_step(sum: int, ai: int, i: int)
    requires
        i <= sum <= 2*i,
        1 <= ai <= 2,
    ensures
        i + 1 <= sum + ai <= 2*(i + 1),
{
}

// Complete the lemma function below
proof fn lemma_i32_add_bounds_preserved_for_small(n: int)
   

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

    // Fill in a block of assertions here to complete the proof

    while (i < N as usize) 
        // Fill in loop invariants here
    {  
        a.set(i, b[i] + 1);

        // Fill in a block of assertions here to complete the proof

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

        proof {
            let sumi: int = sum as int;
            let old_sum: int = (sumi - (a[(i as int)] as int));
            lemma_outer_sum_step(old_sum, (a[(i as int)] as int), (i as int));
            assert((i as int) + 1 <= sumi <= 2*((i as int) + 1));

            assert((i as int) + 1 <= (N as int)) by {
                assert(i < N as usize);
            }

            assert(sumi <= 2*(N as int)) by {
                assert(2*((i as int) + 1) <= 2*(N as int));
                assert(sumi <= 2*((i as int) + 1));
            }
        }

        i = i + 1;
    }  

    // Fill in a block of assertions here to complete the proof

    sum
}
}