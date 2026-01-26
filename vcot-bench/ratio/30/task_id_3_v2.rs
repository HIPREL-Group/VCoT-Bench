use vstd::prelude::*;

fn main() {
}

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

proof fn lemma_exists_intro_divisor(n: u64, k: u64)
    requires
        2 <= k,
        k < n,
        (n % k) == 0,
    ensures
        exists|w: int| 2 <= w < n && is_divisible(n as int, w),
{
    let w: int = k as int;
    assert(2 <= w) by {
        assert(2 <= k);
    }
    assert(w < n as int) by {
        assert(k < n);
    }
    assert(is_divisible(n as int, w)) by {
        assert(((n as int) % w) == 0) by {
            assert((n % k) == 0);
        }
    }
    assert(2 <= w < n as int && is_divisible(n as int, w));
}

proof fn lemma_no_divisor_prefix_extend(n: int, i: u64)
    requires
        2 <= i,
        forall|k: int| 2 <= k < (i as int) ==> !is_divisible(n, k),
        (n % (i as int)) != 0,
    ensures
        forall|k: int| 2 <= k < ((i + 1) as int) ==> !is_divisible(n, k),
{
    assert(forall|k: int| 2 <= k < ((i + 1) as int) ==> !is_divisible(n, k)) by {
        assert forall|k: int| 2 <= k < ((i + 1) as int) implies !is_divisible(n, k) by {
            if k < (i as int) {
                assert(2 <= k < (i as int));
                assert(!is_divisible(n, k));
            } else {
                assert(k == (i as int)) by {
                    assert(k <= (i as int)) by {
                        assert(k < ((i + 1) as int));
                    }
                    assert((i as int) <= k) by {
                        assert(!(k < (i as int)));
                    }
                }
                assert((n % k) != 0) by {
                    assert(k == (i as int));
                    assert((n % (i as int)) != 0);
                }
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn is_non_prime(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
{
    if n <= 1 {
        return true;
    }
    let mut index = 2;
    while index < n
        invariant
            2 <= index,
            forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
    {
        if ((n % index) == 0) {
            // Fill in a block of assertions here to complete the proof
            return true;
        }
        proof {
            lemma_no_divisor_prefix_extend(n as int, index);
        }
        index += 1;
    }

    // Fill in a block of assertions here to complete the proof
    false
}

} // verus!