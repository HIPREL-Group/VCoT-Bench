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

// Complete the lemma function below
proof fn triangle_is_monotonic(i: nat, j: nat)
   

proof fn lemma_triangle_step_upper_bound(n: nat, idx1: nat)
    requires
        idx1 <= n,
        triangle(n) < 0x1_0000_0000,
    ensures
        triangle(idx1) <= triangle(n),
{
    triangle_is_monotonic(idx1, n);
}

proof fn lemma_triangle_add_no_overflow(n: nat, idx1: nat, sum: u32)
    requires
        idx1 <= n,
        idx1 > 0, 
        sum == triangle((idx1 - 1) as nat),
        triangle(n) < 0x1_0000_0000,
    ensures
        sum + (idx1 as u32) < 0x1_0000_0000,
{
    lemma_triangle_step_upper_bound(n, idx1);

    assert(triangle((idx1 - 1) as nat) + idx1 == triangle(idx1)) by {
        assert(triangle(idx1) == idx1 + triangle((idx1 - 1) as nat));
    }

    assert(triangle(idx1) <= triangle(n)) by {
        triangle_is_monotonic(idx1, n);
    }

    assert(triangle(idx1) < 0x1_0000_0000) by {
        assert(triangle(idx1) <= triangle(n));
        assert(triangle(n) < 0x1_0000_0000);
    }

    assert(sum + (idx1 as u32) < 0x1_0000_0000) by {
        assert(sum == triangle((idx1 - 1) as nat));
        assert(triangle((idx1 - 1) as nat) + idx1 == triangle(idx1));

        assert(sum + (idx1 as u32) == triangle(idx1)) by {
            assert(sum + (idx1 as u32) == triangle((idx1 - 1) as nat) + idx1);
        };

        assert(triangle(idx1) < 0x1_0000_0000);
    }
}

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

        assert(*sum == triangle(idx as nat)) by {
            assert(*sum == triangle((idx - 1) as nat) + idx) by {
                assert(*sum == triangle((idx - 1) as nat) + idx);
            }
            assert(triangle(idx as nat) == idx as nat + triangle((idx - 1) as nat)) by {
                assert(idx as nat > 0);
                assert(triangle(idx as nat) == idx as nat + triangle((idx as nat - 1) as nat));
                assert((idx - 1) as nat == (idx as nat - 1) as nat);
            }
        }

        tail_triangle(n, idx, sum);
    }
}
}