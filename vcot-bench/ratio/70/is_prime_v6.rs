use vstd::prelude::*;

fn main() {}
verus! {

spec fn divides(factor: nat, candidate: nat) -> bool {
    candidate % factor == 0
}

spec fn is_prime(candidate: nat) -> bool {
    &&& 1 < candidate
    &&& forall|factor: nat| 1 < factor && factor < candidate ==> !divides(factor, candidate)
}

// Complete the lemma function below
proof fn lemma_is_prime_false_if_has_divisor(candidate: nat, factor: nat)
   

proof fn lemma_loop_inv_implies_not_prime_when_current_factor_divides(candidate: u64, factor: u64)
    requires
        1 < candidate,
        1 < factor,
        factor < candidate,
        divides(factor as nat, candidate as nat),
    ensures
        !is_prime(candidate as nat),
{
    lemma_is_prime_false_if_has_divisor(candidate as nat, factor as nat);
}

// Complete the lemma function below
proof fn lemma_strict_increase_preserves_forall_divides(candidate: u64, old_factor: u64, new_factor: u64)
   

proof fn lemma_exit_loop_gives_all_nondivisors(candidate: u64, factor: u64)
    requires
        1 < candidate,
        factor >= candidate,
        factor <= candidate,
        forall|sf: nat| 1 < sf && sf < factor ==> !divides(sf, candidate as nat),
    ensures
        is_prime(candidate as nat),
{
    assert(1 < candidate as nat);
    assert(forall|f: nat| 1 < f && f < candidate as nat ==> !divides(f, candidate as nat)) by {
        let f = arbitrary::<nat>();
        if 1 < f && f < candidate as nat {
            assert(f < factor);
            assert(!divides(f, candidate as nat));
        }
    }
    assert(is_prime(candidate as nat));
}

#[verifier::exec_allows_no_decreases_clause]
fn test_prime(candidate: u64) -> (result: bool)
    requires
        1 < candidate,
    ensures
        result == is_prime(candidate as nat),
{
    let mut factor: u64 = 2;
    while factor < candidate
        // Fill in loop invariants here
    {
        if candidate % factor == 0 {
            // Fill in a block of assertions here to complete the proof
            return false;
        }
        // Fill in a block of assertions here to complete the proof
        factor = factor + 1;
    }
    // Fill in a block of assertions here to complete the proof
    true
}

} // verus!