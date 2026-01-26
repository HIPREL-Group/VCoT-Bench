use vstd::prelude::*;

fn main() {
}

verus! {

pub open spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}

// Complete the lemma function below
proof fn lemma_len_drop_last_is_len_minus_one<A>(s: Seq<A>)
   

proof fn lemma_take_drop_last_equiv_subrange<A>(s: Seq<A>, i: int)
    requires
        i > 0,
        0 <= i,
        i <= s.len(),
    ensures
        s.subrange(0, i - 1) == s.subrange(0, i).drop_last(),
{
    assert forall|j: int|
        0 <= j < (i - 1)
    implies
        s.subrange(0, i - 1).index(j) == s.subrange(0, i).drop_last().index(j)
    by {
        assert(j < i);
        assert(s.subrange(0, i - 1).index(j) == s.index(j));
        assert(s.subrange(0, i).drop_last().index(j) == s.subrange(0, i).index(j));
        assert(s.subrange(0, i).index(j) == s.index(j));
    };

    assert(s.subrange(0, i).drop_last() == s.subrange(0, i - 1));
    assert(s.subrange(0, i - 1) == s.subrange(0, i).drop_last());
}

// Complete the lemma function below
proof fn lemma_seq_take_succ_drop_last<A>(s: Seq<A>, i: int)
   

// Complete the lemma function below
proof fn lemma_take_all_is_identity<A>(s: Seq<A>)
    

// Complete the lemma function below
proof fn lemma_remove_duplicates_loop_step(arr: Seq<i32>, key: i32, index: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }
    // Fill in a block of assertions here to complete the proof;
    counter
}

#[verifier::exec_allows_no_decreases_clause]
fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();

    assert(arr@.take(0int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1) == Seq::<
        i32,
    >::empty());

    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }

        // Fill in a block of assertions here to complete the proof
        index += 1;
    }
    // Fill in a block of assertions here to complete the proof;
    unique_arr
}

} // verus!