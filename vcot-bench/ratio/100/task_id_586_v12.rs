use vstd::prelude::*;
fn main() {
}

verus! {
use vstd::assert_seqs_equal;

// Complete the lemma function below
proof fn lemma_seq_push_extends_subrange<T>(s: Seq<T>, a: T, start: int, end_: int)
   

// Complete the lemma function below
proof fn lemma_seq_ext_eq_trans<A>(s1: Seq<A>, s2: Seq<A>, s3: Seq<A>)
   

#[verifier::exec_allows_no_decreases_clause]
fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        new_list@ == list@.subrange((n as int), (list@.len() as int)).add(list@.subrange(0, (n as int))),
{
    let mut new_list = Vec::new();

    // Fill in a block of assertions here to complete the proof;

    let mut index = n;
    while index < list.len()
        // Fill in loop invariants here
    {
        let prev_index = index;

        // Fill in a block of assertions here to complete the proof;

        new_list.push(list[index]);
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof;

    let mut index = 0;
    while index < n
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof

        let prev_index = index;

        // Fill in a block of assertions here to complete the proof;

        new_list.push(list[index]);
        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }

    // Fill in a block of assertions here to complete the proof

    new_list
}

}