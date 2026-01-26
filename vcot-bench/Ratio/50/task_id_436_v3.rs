use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_take_drop_last_succ(arr: Seq<i32>, i: int)
   

proof fn lemma_filter_take_step(arr: Seq<i32>, i: int)
    requires
        0 <= i < arr.len(),
    ensures
        arr.take(i + 1).filter(|x: i32| x < 0)
        ==
        if arr[i] < 0 {
            arr.take(i).filter(|x: i32| x < 0).push(arr[i])
        } else {
            arr.take(i).filter(|x: i32| x < 0)
        },
{
    assert(arr.take(i + 1) == arr.take(i).push(arr[i]));
    
    let s = arr.take(i + 1);
    assert(s.len() > 0);
    assert(s.last() == arr[i]);
    assert(s.drop_last() == arr.take(i));

    reveal(Seq::filter);

    if arr[i] < 0 {
        assert(arr.take(i + 1).filter(|x: i32| x < 0)
            == arr.take(i).filter(|x: i32| x < 0).push(arr[i]));
    } else {
        assert(arr.take(i + 1).filter(|x: i32| x < 0)
            == arr.take(i).filter(|x: i32| x < 0));
    }
}

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
        invariant
            0 <= index <= arr.len(),
            negative_list@ == arr@.take(index as int).filter(|x: i32| x < 0),
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