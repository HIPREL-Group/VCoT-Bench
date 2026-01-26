#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

fn main() {
}

verus! {

spec fn max_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}

proof fn lemma_subrange_drop_last_equiv<A>(s: Seq<A>, i: int, j: int)
    requires
        0 <= i,
        i < j,
        j <= s.len(),
    ensures
        s.subrange(i, j - 1) == s.subrange(i, j).drop_last(),
{
    assert(s.subrange(i, j).len() == j - i);
    assert(s.subrange(i, j).drop_last().len() == j - i - 1);
    assert(s.subrange(i, j - 1).len() == (j - 1) - i);

    assert(forall|k: int|
        0 <= k < s.subrange(i, j - 1).len()
        ==> s.subrange(i, j - 1)[k] == s.subrange(i, j).drop_last()[k]
    ) by {
        assert(forall|k: int|
            0 <= k < s.subrange(i, j - 1).len()
            ==> #[trigger] s.subrange(i, j - 1)[k] == s[i + k]
        );
        assert(forall|k: int|
            0 <= k < s.subrange(i, j).drop_last().len()
            ==> #[trigger] s.subrange(i, j).drop_last()[k] == s.subrange(i, j)[k]
        );
        assert(forall|k: int|
            0 <= k < s.subrange(i, j).len()
            ==> #[trigger] s.subrange(i, j)[k] == s[i + k]
        );
    };

    assert(s.subrange(i, j - 1) =~= s.subrange(i, j).drop_last());
}

#[verifier::exec_allows_no_decreases_clause]
fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;

    while index < arr.len()
        invariant
            1 <= index <= arr.len(),
            i32::MIN / 2 < min_val < i32::MAX / 2,
            i32::MIN / 2 < max_val < i32::MAX / 2,
            max_val == max_rcur(arr@.subrange(0, (index as int))),
            min_val == min_rcur(arr@.subrange(0, (index as int))),
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;

        proof {
            let j: int = index as int;

            lemma_subrange_drop_last_equiv(arr@, 0, j);

            assert((index - 1) as int == j - 1);
            assert(arr@.subrange(0, (index as int)) == arr@.subrange(0, j));
        }
        assert(arr@.subrange(0, (index - 1) as int) == arr@.subrange(0, (index as int)).drop_last());
    }
    proof {
        assert((index as int) == arr@.len());
    }
    assert(arr@ == arr@.subrange(0, (index as int)));
    max_val - min_val
}

}