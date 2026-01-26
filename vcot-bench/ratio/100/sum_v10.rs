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
    

// Complete the lemma function below
proof fn lemma_nat_cast_i_minus_1_add_1(i: u64)
   

// Complete the lemma function below
proof fn lemma_arith_sum_int_lt_10000_implies_u64_no_overflow(n: u64)
   

// Complete the lemma function below
proof fn lemma_loop_body_update_sum(
    iprev: nat,
    sum_prev: u64,
    i_next: u64,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        arith_sum_int(n as nat) < 10000,
    ensures
        arith_sum_int(n as nat) == sum,
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;

    // Fill in a block of assertions here to complete the proof

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