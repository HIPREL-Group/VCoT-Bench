use vstd::prelude::*;
fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_vec_push_view_maintains_subrange<T>(
    v_before: Seq<T>,
    a: T,
    base: Seq<T>,
    i: int,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn split_array(list: &Vec<i32>, l: usize) -> (new_list: (Vec<i32>, Vec<i32>))
    requires
        list@.len() > 0,
        0 < l < list@.len(),
    ensures
        new_list.0@ == list@.subrange(0, (l as int)),
        new_list.1@ == list@.subrange((l as int), (list.len() as int)),
{
    let mut part1: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < l
        // Fill in loop invariants here
    {
        let ghost part1_before = part1@;
        let ghost idx_i: int = (index as int);
        // Fill in a block of assertions here to complete the proof;

        part1.push(list[index]);

        let ghost pushed = part1@;

        // Fill in a block of assertions here to complete the proof

        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }
    let mut part2: Vec<i32> = Vec::new();
    index = l;
    while index < list.len()
        // Fill in loop invariants here
    {
        let ghost part2_before = part2@;
        let ghost start: int = (l as int);
        let ghost idx_i: int = (index as int);
        // Fill in a block of assertions here to complete the proof;

        part2.push(list[index]);

        let ghost pushed = part2@;

        // Fill in a block of assertions here to complete the proof

        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }

    assert(part1@ =~= list@.subrange(0, (l as int)));
    assert(part2@ =~= list@.subrange((l as int), (list.len() as int)));

    (part1, part2)
}

}