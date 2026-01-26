use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_take_drop_last_step<A>(s: Seq<A>, i: int)
   

// Complete the lemma function below
proof fn lemma_filter_push_keeps_last_u32(s: Seq<u32>, x: u32)
    

// Complete the lemma function below
proof fn lemma_filter_push_even_u32(s: Seq<u32>, x: u32)
   

// Complete the lemma function below
proof fn lemma_filter_take_push_step_u32(s: Seq<u32>, i: int)
   

// Complete the lemma function below
proof fn lemma_filter_index_implies_pred_u32(s: Seq<u32>, j: int)
   

// Complete the lemma function below
proof fn lemma_seq_eq_filter_all_satisfy_u32(s: Seq<u32>)
   

// Complete the lemma function below
proof fn lemma_vec_view_take_len<A>(v: &Vec<A>)
    

// Complete the lemma function below
proof fn lemma_vec_index_view_eq<A>(v: &Vec<A>)
    

#[verifier::exec_allows_no_decreases_clause]
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures
        if let Some(idx) = index {
            &&& arr@.take((idx as int)) == arr@.take((idx as int)).filter(|x: u32| x % 2 == 0)
            &&& arr[(idx as int)] % 2 != 0
        } else {
            forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
        },
{
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            arr@.take((index as int)) =~= arr@.take((index as int)).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 != 0) {
            return Some(index);
        }

        assert(arr[(index as int)] % 2 == 0);

        assert(arr@.take(((index + 1) as int)).drop_last() == arr@.take((index as int))) by {
            lemma_take_drop_last_step(arr@, (index as int));
        }

        reveal(Seq::filter);

        assert(arr@.take(((index + 1) as int)) =~= arr@.take(((index + 1) as int)).filter(|x: u32| x % 2 == 0)) by {
            assert(arr@.take((index as int)) =~= arr@.take((index as int)).filter(|x: u32| x % 2 == 0));
            assert(arr@[(index as int)] % 2 == 0);
            lemma_filter_take_push_step_u32(arr@, (index as int));
        }

        index += 1;
    }

    assert(arr@ == arr@.take((input_len as int))) by {
        assert(input_len == arr.len());
        lemma_vec_view_take_len(arr);
    }

    assert(forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)) by {
        assert(arr@.take((arr.len() as int)) =~= arr@.take((arr.len() as int)).filter(|x: u32| x % 2 == 0)) by {
            assert(arr@.take((index as int)) =~= arr@.take((index as int)).filter(|x: u32| x % 2 == 0));
            assert(index == arr.len());
        };

        assert(arr@ =~= arr@.filter(|x: u32| x % 2 == 0)) by {
            assert(arr@ == arr@.take((arr.len() as int)));
            assert(arr@.filter(|x: u32| x % 2 == 0) == arr@.take((arr.len() as int)).filter(|x: u32| x % 2 == 0));
        }

        lemma_seq_eq_filter_all_satisfy_u32(arr@);

        assert(forall|k: int| 0 <= k < arr.len() ==> (arr@[k] % 2 == 0)) by { };

        assert(forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)) by {
            lemma_vec_index_view_eq(arr);
        };
    };

    None
}

} // verus!