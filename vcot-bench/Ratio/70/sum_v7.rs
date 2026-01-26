#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

spec fn arith_sum_int(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + arith_sum_int((i - 1) as nat) }
}

// Complete the lemma function below
proof fn lemma_arith_sum_monotonic(i: nat, j: nat)
   

// Complete the lemma function below
proof fn lemma_arith_sum_step(i: nat)
    

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

// Complete the lemma function below
proof fn lemma_arith_sum_int_lt_10000_implies_u64_no_overflow(n: u64)
   

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

        // Fill in a block of assertions here to complete the proof
    }
    sum
}

} // verus!