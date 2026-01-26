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

// Complete the lemma function below
proof fn lemma_subrange_drop_last<T>(s: Seq<T>, j: int, k: int)
   

proof fn lemma_subrange_push_last_i32(s: Seq<i32>, k: int)
    requires
        0 < k <= s.len(),
    ensures
        s.subrange(0, k) == s.subrange(0, k - 1).push(s[k - 1]),
{
    let t = s.subrange(0, k);
    let u = s.subrange(0, k - 1);

    assert(u.push(s[k - 1]).len() == u.len() + 1);

    assert(forall|i: int| 0 <= i < k ==> t[i] == u.push(s[k - 1])[i]) by {
        let i: int = arbitrary();
        if 0 <= i < k {
            if i < k - 1 {
                assert(u.push(s[k - 1])[i] == u[i]);
                assert(u[i] == s[i]);
                assert(t[i] == s[i]);
            } else {
                assert(i == k - 1);
                assert(u.push(s[k - 1])[i] == s[k - 1]);
                assert(t[i] == s[k - 1]);
            }
        }
    };

    assert(t =~= u.push(s[k - 1]));
}

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
    
    proof {
        assert(min_val == min_rcur(arr@.subrange(0, 1)));
        assert(max_val == max_rcur(arr@.subrange(0, 1)));
    }

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
    proof {
        assert(arr@.subrange(0, (arr.len() as int)) =~= arr@);
    }
    max_val + min_val
}

} // verus!