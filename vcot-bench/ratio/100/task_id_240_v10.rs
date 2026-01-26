use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_subrange_add_whole<A>(s: Seq<A>, n: int)
   

// Complete the lemma function below
proof fn lemma_seq_add_append_one<A>(s1: Seq<A>, s2: Seq<A>, a: A)
    

// Complete the lemma function below
proof fn lemma_subrange_all<A>(s: Seq<A>)
    

#[verifier::exec_allows_no_decreases_clause]
fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
    requires
        first.len() > 0,
    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
{
    let mut replaced_list = Vec::new();
    let first_end = first.len() - 1;
    let mut index = 0;

    // Fill in a block of assertions here to complete the proof

    while index < first_end
        // Fill in loop invariants here
    {
        replaced_list.push(first[index]);
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }
    index = 0;

    // Fill in a block of assertions here to complete the proof

    while index < second.len()
        // Fill in loop invariants here
    {
        replaced_list.push(second[index]);
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof;

    replaced_list
}

}