use vstd::prelude::*;
fn main() {
}

verus! {

uninterp spec fn uHi(x: int) -> int;

spec fn uInv(n: int, x: int) -> bool {
    0 <= x && x < uHi(n)
}

proof fn lemma_u64_inv_from_bounds(x: int)
    requires
        0 <= x,
        x < uHi(64),
    ensures
        uInv(64, x),
{
    assert(uInv(64, x));
}

#[verifier::exec_allows_no_decreases_clause]
fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        reversed_list@ == list@.subrange(0, n as int).reverse().add(
            list@.subrange(n as int, list.len() as int),
        ),
{
    let mut reversed_list = Vec::new();
    let mut index = 0;
    while index < n
        // Fill in loop invariants here
    {
        reversed_list.push(list[n - 1 - index]);

        assert(forall|k: int| 0 <= k < index + 1 ==> reversed_list[k] == list[n - 1 - k]) by {
            assert(forall|k: int| 0 <= k < index ==> reversed_list[k] == list[n - 1 - k]);
            assert(reversed_list[index as int] == list[n - 1 - index]);
        }

        index += 1;
    }
    index = n;

    assert(reversed_list@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, index as int))) by {
        assert(list@.subrange(n as int, index as int) == Seq::<i32>::empty());
        assert(list@.subrange(0, n as int).reverse().add(Seq::<i32>::empty()) == list@.subrange(0, n as int).reverse());
        
        let expected = list@.subrange(0, n as int).reverse();
        assert(reversed_list@ =~= expected) by {
            assert(reversed_list.len() == n);
            assert(forall|k: int| 0 <= k < n as int ==> reversed_list[k] == list[n - 1 - k]);
            assert(forall|k: int| 0 <= k < n as int ==> expected[k] == list[n - 1 - k]);
        }
    }

    while index < list.len()
        invariant
            n <= index <= list.len(),
            reversed_list@ =~= list@.subrange(0, n as int).reverse().add(
                list@.subrange(n as int, index as int),
            ),
    {
        reversed_list.push(list[index]);
        index += 1;
    }
    reversed_list
}

} // verus!