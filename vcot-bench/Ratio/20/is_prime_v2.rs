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

proof fn lemma_is_prime_false_if_has_divisor(candidate: nat, factor: nat)
    requires
        1 < candidate,
        1 < factor,
        factor < candidate,
        divides(factor, candidate),
    ensures
        !is_prime(candidate),
{
    assert(!is_prime(candidate)) by {
        if is_prime(candidate) {
            assert(!divides(factor, candidate));
            assert(divides(factor, candidate));
            assert(false);
        }
    }
}

// Complete the lemma function below
proof fn lemma_loop_inv_implies_not_prime_when_current_factor_divides(candidate: u64, factor: u64)
   

proof fn lemma_strict_increase_preserves_forall_divides(candidate: u64, old_factor: u64, new_factor: u64)
    requires
        new_factor == old_factor + 1,
        forall|sf: nat| 1 < sf && sf < old_factor ==> !divides(sf, candidate as nat),
        candidate % old_factor != 0,
        2 <= old_factor,
    ensures
        forall|sf: nat| 1 < sf && sf < new_factor ==> !divides(sf, candidate as nat),
{
    assert(forall|sf: nat| 1 < sf && sf < new_factor ==> !divides(sf, candidate as nat)) by {
        let sf = arbitrary::<nat>();
        if 1 < sf && sf < new_factor {
            if sf < old_factor {
                assert(!divides(sf, candidate as nat));
            } else {
                assert(sf == old_factor as nat) by {
                    assert(sf < (old_factor as nat) + 1);
                    assert(sf >= old_factor as nat);
                }
                assert(!divides(sf, candidate as nat)) by {
                    assert(candidate % old_factor != 0);
                    assert(!divides(old_factor as nat, candidate as nat));
                }
            }
        }
    }
}

// Complete the lemma function below
proof fn lemma_exit_loop_gives_all_nondivisors(candidate: u64, factor: u64)
   

#[verifier::exec_allows_no_decreases_clause]
fn test_prime(candidate: u64) -> (result: bool)
    requires
        1 < candidate,
    ensures
        result == is_prime(candidate as nat),
{
    let mut factor: u64 = 2;
    while factor < candidate
        invariant
            1 < factor <= candidate,
            forall|smallerfactor: nat|
                1 < smallerfactor < factor ==> !divides(smallerfactor, candidate as nat),
    {
        if candidate % factor == 0 {
            proof {
                lemma_loop_inv_implies_not_prime_when_current_factor_divides(candidate, factor);
            }
            return false;
        }
        proof {
            lemma_strict_increase_preserves_forall_divides(candidate, factor, (factor + 1) as u64);
        }
        factor = factor + 1;
    }
    proof {
        lemma_exit_loop_gives_all_nondivisors(candidate, factor);
    }
    true
}

} // verus!