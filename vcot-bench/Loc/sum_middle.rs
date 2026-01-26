#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

spec fn arith_sum_int(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + arith_sum_int((i - 1) as nat) }
}

proof fn lemma_arith_sum_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        arith_sum_int(i as nat) <= arith_sum_int(j as nat),
    decreases j
{
    if i < j {
        lemma_arith_sum_monotonic(i, (j - 1) as nat);

        assert((j - 1) as nat <= j);
        assert(i <= (j - 1) as nat);

        assert(arith_sum_int(i) <= arith_sum_int((j - 1) as nat));

        assert(arith_sum_int((j - 1) as nat) <= arith_sum_int(j)) by {
            if j == 0 {
                assert(false);
            } else {
                assert(j as nat != 0);
                assert(arith_sum_int(j) == j + arith_sum_int((j - 1) as nat));
                assert(arith_sum_int((j - 1) as nat) <= j + arith_sum_int((j - 1) as nat));
            }
        }

        assert(arith_sum_int(i) <= arith_sum_int(j)) by {
            assert(arith_sum_int(i) <= arith_sum_int((j - 1) as nat));
            assert(arith_sum_int((j - 1) as nat) <= arith_sum_int(j));
        }
    } else {
        assert(i == j);
    }
}

proof fn lemma_arith_sum_step(i: nat)
    ensures
        arith_sum_int((i + 1) as nat) == arith_sum_int(i) + (i + 1),
{
    assert((i + 1) as nat != 0);
    assert(arith_sum_int((i + 1) as nat) == (i + 1) + arith_sum_int(((i + 1) - 1) as nat));
    assert(((i + 1) - 1) as nat == i);
    assert(arith_sum_int((i + 1) as nat) == (i + 1) + arith_sum_int(i));
    assert((i + 1) + arith_sum_int(i) == arith_sum_int(i) + (i + 1));
}

proof fn lemma_nat_cast_i_minus_1_add_1(i: u64)
    requires
        i != 0,
    ensures
        (i as nat) == ((i - 1) as nat) + 1,
{
    let iprev: nat = (i - 1) as nat;
    assert(i == (i - 1) + 1);
    assert((i as nat) == (iprev + 1));
}

proof fn lemma_arith_sum_int_lt_10000_implies_u64_no_overflow(n: u64)
    requires
        arith_sum_int(n as nat) < 10000,
    ensures
        arith_sum_int(n as nat) as u64 == arith_sum_int(n as nat),
{
    assert(10000 <= u64::MAX);
    assert(arith_sum_int(n as nat) <= u64::MAX as nat);
}

proof fn lemma_loop_body_update_sum(
    iprev: nat,
    sum_prev: u64,
    i_next: u64,
)
    requires
        i_next != 0,
        i_next as nat == iprev + 1,
        sum_prev == arith_sum_int(iprev),
    ensures
        sum_prev + i_next == arith_sum_int(i_next as nat),
{
    lemma_arith_sum_step(iprev);
    assert(arith_sum_int(i_next as nat) == arith_sum_int(iprev) + (iprev + 1));
    assert((iprev + 1) as u64 == i_next);
    assert(sum_prev + i_next == arith_sum_int(iprev) + (iprev + 1)) by {
        assert(sum_prev == arith_sum_int(iprev));
    }
    assert(sum_prev + i_next == arith_sum_int(i_next as nat));
}

#[verifier::exec_allows_no_decreases_clause]
fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        arith_sum_int(n as nat) < 10000,
    ensures
        arith_sum_int(n as nat) == sum,
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;

    proof {
        assert(sum == arith_sum_int(i as nat)) by {
            assert(i == 0);
            assert(i as nat == 0);
            assert(sum == 0);
            assert(arith_sum_int(0) == 0);
        }
        assert(i <= n);
        assert(arith_sum_int(n as nat) < 10000);
    }

    while i < n
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof;

        let sum_before: u64 = sum;
        let i_before: u64 = i;

        i = i + 1;

        // Fill in a block of assertions here to complete the proof

        sum = sum + i;

        assert(sum == arith_sum_int(i as nat)) by {
            let iprev: nat = (i - 1) as nat;
            assert(i != 0);

            assert(i as nat == iprev + 1) by {
                lemma_nat_cast_i_minus_1_add_1(i);
            }

            lemma_arith_sum_step(iprev);
            assert(arith_sum_int(i as nat) == arith_sum_int(iprev) + (iprev + 1));

            assert(sum_before == arith_sum_int(iprev)) by {
                assert(sum_before == arith_sum_int(i_before as nat));
                assert(i_before == i - 1);
                assert(iprev == i_before as nat);
            }

            assert(sum == arith_sum_int(iprev) + (iprev + 1)) by {
                assert(sum == sum_before + i);
                assert(sum_before == arith_sum_int(iprev));
                assert(i == (iprev + 1) as u64);
            }

            assert(sum == arith_sum_int(i as nat));
        }
    }
    sum
}

} // verus!