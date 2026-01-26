use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_take_drop_last_step<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.take(i + 1).drop_last() == s.take(i),
{
    assert(s.take((i + 1)).drop_last() =~= s.take(i)) by {
        reveal(Seq::take);
        reveal(Seq::drop_last);
    }
}

// Complete the lemma function below
proof fn lemma_filter_push_keeps_last_u32(s: Seq<u32>, x: u32)
    

// Complete the lemma function below
proof fn lemma_filter_push_even_u32(s: Seq<u32>, x: u32)
   

// Complete the lemma function below
proof fn lemma_filter_take_push_step_u32(s: Seq<u32>, i: int)
   

proof fn lemma_filter_index_implies_pred_u32(s: Seq<u32>, j: int)
    requires
        0 <= j < s.filter(|x: u32| x % 2 == 0).len(),
    ensures
        s.filter(|x: u32| x % 2 == 0)[j] % 2 == 0,
{
    reveal(Seq::filter);
}

// Complete the lemma function below
proof fn lemma_seq_eq_filter_all_satisfy_u32(s: Seq<u32>)
   

// Complete the lemma function below
proof fn lemma_vec_view_take_len<A>(v: &Vec<A>)
    

proof fn lemma_vec_index_view_eq<A>(v: &Vec<A>)
    ensures
        forall|k: int| 0 <= k < v.len() ==> v[k] == v@[k],
{
    assert(forall|k: int| 0 <= k < v.len() ==> v[k] == v@[k]) by { }
}

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
        // Fill in loop invariants here
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

    // Fill in a block of assertions here to complete the proof;

    None
}

} // verus!