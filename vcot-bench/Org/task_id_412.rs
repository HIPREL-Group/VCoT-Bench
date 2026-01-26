use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_take0_filter_empty(arr: Seq<u32>)
    ensures
        arr.take(0).filter(|x: u32| x % 2 == 0) == Seq::<u32>::empty(),
{
    assert(arr.take(0) == Seq::<u32>::empty());
    assert(Seq::<u32>::empty().filter(|x: u32| x % 2 == 0) == Seq::<u32>::empty()) by {
        reveal(Seq::filter);
    }
}

proof fn lemma_take_drop_last(arr: Seq<u32>, i: int)
    requires
        i >= 0,
        i < arr.len(),
    ensures
        arr.take(i + 1).drop_last() == arr.take(i),
{
    assert(forall|k: int| 0 <= k < i ==> #[trigger] arr.take(i + 1).drop_last()[k] == arr.take(i)[k]) by {
        assert(forall|k: int| 0 <= k < i ==> #[trigger] arr.take(i + 1).drop_last()[k] == arr.take(i + 1)[k]) by { }
        assert(forall|k: int| 0 <= k < i ==> #[trigger] arr.take(i + 1)[k] == arr[k]) by { }
        assert(forall|k: int| 0 <= k < i ==> #[trigger] arr.take(i)[k] == arr[k]) by { }
    }

    assert(arr.take(i + 1).drop_last() == arr.take(i));
}

proof fn lemma_take_len_full(arr: Seq<u32>)
    ensures
        arr.take((arr.len() as int)) == arr,
{
    assert(forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr.take((arr.len() as int))[i] == arr[i]) by { }
    assert(arr.take((arr.len() as int)) == arr);
}

proof fn lemma_take_succ_push(arr: Seq<u32>, i: int)
    requires
        0 <= i,
        i < arr.len(),
    ensures
        arr.take(i + 1) == arr.take(i).push(arr[i]),
{
    assert(forall|k: int| 0 <= k < i + 1 ==> #[trigger] arr.take(i + 1)[k] == arr.take(i).push(arr[i])[k]) by {
        assert(forall|k: int| 0 <= k < i ==> #[trigger] arr.take(i + 1)[k] == arr.take(i).push(arr[i])[k]) by {
            assert(forall|k: int| 0 <= k < i ==> #[trigger] arr.take(i + 1)[k] == arr[k]);
            assert(forall|k: int| 0 <= k < i ==> #[trigger] arr.take(i)[k] == arr[k]);
        };
        assert(arr.take(i + 1)[i] == arr[i]) by { }
        assert(arr.take(i).push(arr[i])[i] == arr[i]);
    }

    assert(arr.take(i + 1) == arr.take(i).push(arr[i]));
}

#[verifier::exec_allows_no_decreases_clause]
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    proof { lemma_take0_filter_empty(arr@); }

    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            even_list@ == arr@.take((index as int)).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 == 0) {
            even_list.push(arr[index]);
        }

        assert(arr@.take(((index + 1) as int)).drop_last() == arr@.take((index as int))) by {
            lemma_take_drop_last(arr@, (index as int));
        };

        proof { reveal(Seq::filter); }

        if arr[index] % 2 == 0 {
            assert(arr@.take(((index + 1) as int))
                == arr@.take((index as int)).push(arr[(index as int)])) by {
                lemma_take_succ_push(arr@, (index as int));
            }
            assert(
                arr@.take(((index + 1) as int)).filter(|x: u32| x % 2 == 0)
                == arr@.take((index as int)).filter(|x: u32| x % 2 == 0).push(arr[(index as int)])
            ) by {
                reveal(Seq::filter);
            }
        } else {
            assert(
                arr@.take(((index + 1) as int)).filter(|x: u32| x % 2 == 0)
                == arr@.take((index as int)).filter(|x: u32| x % 2 == 0)
            ) by {
                reveal(Seq::filter);
            }
        }

        index += 1;
    }

    assert(arr@ == arr@.take((input_len as int))) by {
        lemma_take_len_full(arr@);
    };

    even_list
}

}