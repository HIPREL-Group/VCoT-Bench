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

    proof {
        reveal(Seq::filter);
        assert(arr@.take(0).len() == 0);
        assert(arr@.take(0).filter(|x: i32| x < 0) == Seq::<i32>::empty());
    }

    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] < 0) {
            negative_list.push(arr[index]);
        }

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }

    assert(arr@ == arr@.take(input_len as int));
    negative_list
}

}