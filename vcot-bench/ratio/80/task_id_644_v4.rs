use vstd::prelude::*;
fn main() {
}

verus! {

uninterp spec fn uHi(x: int) -> int;

spec fn uInv(n: int, x: int) -> bool {
    0 <= x && x < uHi(n)
}

// Complete the lemma function below
proof fn lemma_u64_inv_from_bounds(x: int)
   

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

    // Fill in a block of assertions here to complete the proof

    while index < list.len()
        // Fill in loop invariants here
    {
        reversed_list.push(list[index]);
        index += 1;
    }
    reversed_list
}

} // verus!