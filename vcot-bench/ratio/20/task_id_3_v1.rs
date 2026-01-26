use vstd::prelude::*;

fn main() {
}

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

// Complete the lemma function below
proof fn lemma_exists_intro_divisor(n: u64, k: u64)
   

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
            proof {
                lemma_exists_intro_divisor(n, index);
            }
            return true;
        }
        proof {
            lemma_no_divisor_prefix_extend(n as int, index);
        }
        index += 1;
    }

    assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)) by {
        assert(index >= n);
        assert(forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k));
        assert forall|k: int| 2 <= k < n implies !is_divisible(n as int, k) by {
            assert(2 <= k < index) by {
                assert(k < n);
                assert(n <= index);
            }
            assert(!is_divisible(n as int, k));
        }
    }
    assert(!(exists|k: int| 2 <= k < n && is_divisible(n as int, k))) by {
        assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
        assert(!(exists|k: int| 2 <= k < n && is_divisible(n as int, k))) by {
            if exists|k: int| 2 <= k < n && is_divisible(n as int, k) {
                let k = choose|k: int| 2 <= k < n && is_divisible(n as int, k);
                assert(2 <= k < n && is_divisible(n as int, k));
                assert(!is_divisible(n as int, k)) by {
                    assert(forall|t: int| 2 <= t < n ==> !is_divisible(n as int, t));
                }
                assert(false);
            }
        }
    }
    false
}

} // verus!