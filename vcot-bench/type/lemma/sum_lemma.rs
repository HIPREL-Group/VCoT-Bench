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
        invariant
            i <= n,
            sum == arith_sum_int(i as nat),
            arith_sum_int(n as nat) < 10000,
    {
        assert(i + 1 <= n);

        let sum_before: u64 = sum;
        let i_before: u64 = i;

        i = i + 1;

        assert(i <= n);

        assert(sum + i <= arith_sum_int(n as nat)) by {
            lemma_arith_sum_monotonic(i as nat, n as nat);

            let iprev: nat = (i - 1) as nat;
            assert(i != 0);

            assert(i as nat == iprev + 1) by {
                lemma_nat_cast_i_minus_1_add_1(i);
            }

            lemma_arith_sum_monotonic(iprev, n as nat);

            assert(sum_before == arith_sum_int(i_before as nat));
            assert(i_before + 1 == i);
            assert(i_before < n);
            assert(i_before as nat + 1 == i as nat);

            assert(sum == arith_sum_int(iprev)) by {
                assert(i_before + 1 == i);
                assert(i_before == i - 1);
                assert(iprev == i_before as nat);
                assert(sum == sum_before);
                assert(sum_before == arith_sum_int(i_before as nat));
            }

            lemma_arith_sum_step(iprev);

            assert(sum + i <= arith_sum_int(i as nat) as u64) by {
                lemma_loop_body_update_sum(iprev, sum, i);
                assert(sum + i == arith_sum_int(i as nat));
            }

            assert(sum + i <= arith_sum_int(n as nat) as u64);

            lemma_arith_sum_int_lt_10000_implies_u64_no_overflow(n);
            assert(arith_sum_int(n as nat) as u64 == arith_sum_int(n as nat));
            assert(sum + i <= arith_sum_int(n as nat));
        }

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