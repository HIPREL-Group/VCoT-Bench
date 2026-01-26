use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_take_drop_last_succ(arr: Seq<i32>, i: int)
    requires
        0 <= i < arr.len(),
    ensures
        arr.take(i + 1).drop_last() == arr.take(i),
{
    assert(i + 1 >= 0);

    assert(arr.take(i + 1) == arr.take(i).push(arr[i]));
    assert(arr.take(i + 1).drop_last() == arr.take(i).push(arr[i]).drop_last());
    reveal(Seq::drop_last);
    assert(arr.take(i).push(arr[i]).drop_last() == arr.take(i));
    assert(arr.take(i + 1).drop_last() == arr.take(i));
}

// Complete the lemma function below
proof fn lemma_filter_take_step(arr: Seq<i32>, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    let mut negative_list: Vec<i32> = Vec::new();
    let input_len = arr.len();

    // Fill in a block of assertions here to complete the proof

    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] < 0) {
            negative_list.push(arr[index]);
        }

        proof {
            lemma_take_drop_last_succ(arr@, index as int);
        }
        assert(arr@.take((index + 1) as int).drop_last() == arr@.take(index as int));

        proof {
            reveal(Seq::filter);
            lemma_filter_take_step(arr@, index as int);

            if arr@[index as int] < 0 {
                assert(negative_list@ == arr@.take(index as int).filter(|x: i32| x < 0).push(arr@[index as int]));

                assert(arr@.take((index + 1) as int).filter(|x: i32| x < 0)
                    == arr@.take(index as int).filter(|x: i32| x < 0).push(arr@[index as int]));
            } else {
                assert(negative_list@ == arr@.take(index as int).filter(|x: i32| x < 0));

                assert(arr@.take((index + 1) as int).filter(|x: i32| x < 0)
                    == arr@.take(index as int).filter(|x: i32| x < 0));
            }

            assert(negative_list@ == arr@.take((index + 1) as int).filter(|x: i32| x < 0));
        }

        index += 1;
    }

    // Fill in a block of assertions here to complete the proof;
    negative_list
}

}