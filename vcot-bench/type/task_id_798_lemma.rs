use vstd::prelude::*;

fn main() {
}

verus! {

spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

// Complete the lemma function below
proof fn lemma_sum_to_step_by_subrange(arr: Seq<i64>, index: int)
   

// Complete the lemma function below
proof fn lemma_sum_loop_step(arr: Seq<i64>, index: int, sum_prev: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            sum == sum_to(arr@.subrange(0, index as int)),
            forall|j: int|
                0 <= j <= index ==> (i64::MIN * index <= (sum_to(#[trigger] arr@.subrange(0, j)))
                    <= i64::MAX * index),
    {
        assert(
            sum_to(arr@.subrange(0, (index + 1) as int))
                == sum_to(arr@.subrange(0, index as int)) + arr@[index as int]
        ) by {
            lemma_sum_to_step_by_subrange(arr@, index as int);
        };

        sum = sum + arr[index] as i128;
        index += 1;

        assert(sum == sum_to(arr@.subrange(0, index as int))) by {
            assert(index >= 1);
            assert(sum_to(arr@.subrange(0, index as int))
                == sum_to(arr@.subrange(0, (index - 1) as int)) + arr@[(index - 1) as int]) by {
                lemma_sum_to_step_by_subrange(arr@, (index - 1) as int);
            };
        };
    }
    assert(arr@ == arr@.subrange(0, (index as int))) by {
        assert((index as int) == arr@.len());
        let sub = arr@.subrange(0, (index as int));
        assert(sub.len() == arr@.len());
        assert(forall|i: int| 0 <= i < arr@.len() ==> sub[i] == arr@[i]) by {
            assert forall|i: int| 0 <= i < arr@.len() implies sub[i] == arr@[i] by {}
        }
        assert(arr@ =~= sub);
    };
    sum
}

} // verus!