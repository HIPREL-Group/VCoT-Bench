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

proof fn lemma_subrange_drop_last<T>(s: Seq<T>, j: int, k: int)
    requires
        0 <= j,
        j < k,
        k <= s.len(),
    ensures
        s.subrange(j, k).drop_last() == s.subrange(j, k - 1),
{
    assert(s.subrange(j, k).len() == k - j);
    assert(s.subrange(j, k - 1).len() == (k - 1) - j);

    assert(s.subrange(j, k).drop_last().len() == s.subrange(j, k).len() - 1);
    assert(s.subrange(j, k).drop_last().len() == (k - j) - 1);
    assert(s.subrange(j, k).drop_last().len() == (k - 1) - j);
    assert(s.subrange(j, k).drop_last().len() == s.subrange(j, k - 1).len());

    assert(forall|i: int|
        0 <= i < s.subrange(j, k).drop_last().len()
        ==> s.subrange(j, k).drop_last()[i] == s.subrange(j, k - 1)[i]
    ) by {
        let i: int = arbitrary();
        if 0 <= i < s.subrange(j, k).drop_last().len() {
            assert(s.subrange(j, k).drop_last()[i] == s.subrange(j, k)[i]);
            assert(s.subrange(j, k)[i] == s[i + j]);
            assert(s.subrange(j, k - 1)[i] == s[i + j]);
        }
    };

    assert(s.subrange(j, k).drop_last() =~= s.subrange(j, k - 1));
}

// Complete the lemma function below
proof fn lemma_subrange_push_last_i32(s: Seq<i32>, k: int)
   

// Complete the lemma function below
proof fn lemma_max_rcur_push_last_i32(s: Seq<i32>, k: int)
   

// Complete the lemma function below
proof fn lemma_min_rcur_push_last_i32(s: Seq<i32>, k: int)
   

// Complete the lemma function below
proof fn lemma_max_rcur_update_step(arr: Seq<i32>, k: int, old_max: i32)
   

proof fn lemma_min_rcur_update_step(arr: Seq<i32>, k: int, old_min: i32)
    requires
        1 < k <= arr.len(),
        old_min == min_rcur(arr.subrange(0, k - 1)),
    ensures
        min_rcur(arr.subrange(0, k))
            == if arr[k - 1] <= old_min {
                arr[k - 1] as int
            } else {
                old_min as int
            },
{
    lemma_min_rcur_push_last_i32(arr, k);
    if arr[k - 1] <= old_min {
        assert(min(arr[k - 1] as int, old_min as int) == arr[k - 1] as int);
    } else {
        assert(min(arr[k - 1] as int, old_min as int) == old_min as int);
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    
    // Fill in a block of assertions here to complete the proof

    while index < arr.len()
        invariant
            1 <= index <= arr.len(),
            i32::MIN / 2 < min_val < i32::MAX / 2,
            i32::MIN / 2 < max_val < i32::MAX / 2,
            max_val == max_rcur(arr@.subrange(0, index as int)),
            min_val == min_rcur(arr@.subrange(0, index as int)),
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;

        proof {
            let k: int = index as int;
            lemma_min_rcur_update_step(arr@, k, (min_rcur(arr@.subrange(0, k - 1)) as i32));
            lemma_max_rcur_update_step(arr@, k, (max_rcur(arr@.subrange(0, k - 1)) as i32));
        }
    }
    // Fill in a block of assertions here to complete the proof
    max_val + min_val
}

} // verus!