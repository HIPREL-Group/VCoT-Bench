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

proof fn lemma_sum_to_step_by_subrange(arr: Seq<i64>, index: int)
    requires
        0 <= index,
        index < arr.len(),
    ensures
        sum_to(arr.subrange(0, index + 1)) == sum_to(arr.subrange(0, index)) + arr[index],
{
    let s = arr.subrange(0, index + 1);

    assert(s.len() == index + 1);
    assert(s.len() >= 1);

    assert(s.drop_last() == s.subrange(0, s.len() - 1));

    assert(s.len() - 1 == index) by {
        assert(s.len() == index + 1);
    };

    assert(s.subrange(0, s.len() - 1) == arr.subrange(0, index)) by {
        assert(s.subrange(0, s.len() - 1).len() == index);
        assert(arr.subrange(0, index).len() == index);
        assert(forall|t: int| 0 <= t < index ==> s.subrange(0, s.len() - 1)[t] == arr.subrange(0, index)[t]) by {
            assert forall|t: int| 0 <= t < index implies s.subrange(0, s.len() - 1)[t] == arr.subrange(0, index)[t] by {
                let tt = t;
                assert(0 <= tt < s.len() - 1);
                assert(s.subrange(0, s.len() - 1)[tt] == s[tt]);
                assert(s[tt] == arr[tt]);
                assert(arr[tt] == arr.subrange(0, index)[tt]);
            };
        }
        assert(s.subrange(0, s.len() - 1) == arr.subrange(0, index));
    };

    assert(s.drop_last() == arr.subrange(0, index));
    assert(s.last() == arr[index]);

    assert(sum_to(s) == sum_to(s.drop_last()) + s.last());
    assert(sum_to(s) == sum_to(arr.subrange(0, index)) + arr[index]);
}

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
        // Fill in loop invariants here
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