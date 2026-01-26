use vstd::prelude::*;

fn main() {
}

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

proof fn lemma_forall_extend_by_one(n: int, index: u64)
    requires
        2 <= index as int,
        forall|k: int| 2 <= k < index as int ==> !is_divisible(n, k),
        !is_divisible(n, index as int),
    ensures
        forall|k: int| 2 <= k < index as int + 1 ==> !is_divisible(n, k),
{
    assert forall|k: int| 2 <= k < index as int + 1 implies !is_divisible(n, k) by {
        if k < index as int {
            assert(!is_divisible(n, k));
        } else {
            assert(k == index as int) by {
                assert(k < index as int + 1);
                assert(!(k < index as int));
                assert(k <= index as int);
                assert(index as int <= k);
            };
            assert(!is_divisible(n, k));
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn prime_num(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
{
    if n <= 1 {
        return false;
    }
    let mut index = 2;
    while index < n
        invariant
            2 <= index <= n,
            forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k),
    {
        if ((n % index) == 0) {
            // Fill in a block of assertions here to complete the proof;
            return false;
        }

        // Fill in a block of assertions here to complete the proof;

        index += 1;
    }
    true
}

} // verus!