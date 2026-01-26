use vstd::prelude::*;
fn main() {}

verus!{

spec fn triangle(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}

proof fn triangle_is_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        triangle(i) <= triangle(j),
    decreases j
{
    if i < j {
        assert(i <= (j - 1) as nat) by {
            assert(i + 1 <= j) by {
                assert(i < j);
            };
        };

        triangle_is_monotonic(i, (j - 1) as nat);

        assert(triangle(i) <= triangle(j)) by {
            assert(triangle(i) <= triangle((j - 1) as nat));
            assert(triangle((j - 1) as nat) <= triangle(j)) by {
                assert(triangle((j - 1) as nat) <= j + triangle((j - 1) as nat));
            }
        }
    } else {
        assert(i == j);
    }
}

proof fn lemma_triangle_step_upper_bound(n: nat, idx1: nat)
    requires
        idx1 <= n,
        triangle(n) < 0x1_0000_0000,
    ensures
        triangle(idx1) <= triangle(n),
{
    triangle_is_monotonic(idx1, n);
}

// Complete the lemma function below
proof fn lemma_triangle_add_no_overflow(n: nat, idx1: nat, sum: u32)
   

#[verifier::exec_allows_no_decreases_clause]
fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
    requires
        idx <= n,
        *old(sum) == triangle(idx as nat),
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        *sum == triangle(n as nat),
{
    if idx < n {
        let idx = idx + 1;

        assert(*sum == triangle((idx - 1) as nat));

        assert(*sum + idx < 0x1_0000_0000) by {
            lemma_triangle_add_no_overflow(n as nat, idx as nat, *sum);
        }

        *sum = *sum + idx;

        // Fill in a block of assertions here to complete the proof

        tail_triangle(n, idx, sum);
    }
}
}