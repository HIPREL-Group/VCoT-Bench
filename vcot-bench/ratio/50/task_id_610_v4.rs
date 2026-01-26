use vstd::prelude::*;
fn main() {
}

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, (k - 1) as int).add(
            list@.subrange(k as int, (list.len() as int)),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    while index < (k - 1)
        // Fill in loop invariants here
    {
        assert(index < list.len());
        let ghost old = new_list@;
        let a = list[index];
        new_list.push(a);
        // Fill in a block of assertions here to complete the proof;
        index += 1;
    }

    assert(new_list@ == list@.subrange(0, (k - 1) as int));

    let mut index = k;
    while index < list.len()
        invariant
            k <= index <= list.len(),
            0 < k < list@.len(),
            new_list@ =~= list@.subrange(0 as int, (k - 1) as int).add(
                list@.subrange(k as int, (index as int)),
            ),
    {
        assert(index < list.len());
        let ghost old = new_list@;
        let a = list[index];
        new_list.push(a);
        // Fill in a block of assertions here to complete the proof

        index += 1;
    }

    // Fill in a block of assertions here to complete the proof;

    new_list
}

}