use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_take_drop_last_succ(arr: Seq<i32>, i: int)
   

// Complete the lemma function below
proof fn lemma_filter_take_step(arr: Seq<i32>, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    let mut negative_list: Vec<i32> = Vec::new();
    let input_len = arr.len();

    proof {
        reveal(Seq::filter);
        assert(arr@.take(0).len() == 0);
        assert(arr@.take(0).filter(|x: i32| x < 0) == Seq::<i32>::empty());
    }

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

    assert(arr@ == arr@.take(input_len as int));
    negative_list
}

}