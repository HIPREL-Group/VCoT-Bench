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
   

// Complete the lemma function below
proof fn lemma_take_drop_last_equiv_subrange<A>(s: Seq<A>, i: int)
   

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
        invariant
            0 <= index <= arr.len(),
            0 <= counter <= index,
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
    {
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;

        proof {
            let cur = (index as int);
            let prev = cur - 1;

            lemma_take_drop_last_equiv_subrange(arr@, cur);

            assert(prev < arr@.subrange(0, cur).len());
            assert(arr@.subrange(0, cur).index(prev) == arr@.index(prev));
            assert(arr@.subrange(0, cur).last() == arr@.subrange(0, cur).index(cur - 1));
            assert(arr@.subrange(0, cur).last() == arr@.index(prev));
        }
    }
    assert(arr@ == arr@.subrange(0, (index as int)));
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
        invariant
            0 <= index <= arr.len(),
            unique_arr@ == arr@.take(index as int).filter(
                |x: i32| count_frequency_rcr(arr@, x) == 1,
            ),
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }

        proof {
            lemma_remove_duplicates_loop_step(arr@, arr[(index as int)], (index as int));
            assert(arr@.take(((index + 1) as int)).drop_last() == arr@.take((index as int)));

            reveal(Seq::filter);
        }
        index += 1;
    }
    proof {
        lemma_take_all_is_identity(arr@);
    }
    assert(arr@ == arr@.take((input_len as int)));
    unique_arr
}

} // verus!