use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_subrange_ext_eq_implies_index_eq<T>(
    s1: Seq<T>,
    s2: Seq<T>,
    i: int,
)
   

proof fn lemma_subrange_eq_from_pointwise<T>(
    main: Seq<T>,
    sub: Seq<T>,
    idx: int,
    len: int,
)
    requires
        0 <= len,
        0 <= idx,
        idx + len <= main.len(),
        len <= sub.len(),
        forall|k: int| 0 <= k < len ==> main[idx + k] == sub[k],
    ensures
        main.subrange(idx, idx + len) =~= sub.subrange(0, len),
{
    assert(main.subrange(idx, idx + len).len() == len) by { };
    assert(sub.subrange(0, len).len() == len) by { };

    assert(forall|k: int|
        0 <= k < len ==> main.subrange(idx, idx + len)[k] == sub.subrange(0, len)[k]
    ) by {
        assert forall|k: int| 0 <= k < len implies
            main.subrange(idx, idx + len)[k] == sub.subrange(0, len)[k]
        by {
            assert(main.subrange(idx, idx + len)[k] == main[idx + k]) by { };
            assert(sub.subrange(0, len)[k] == sub[k]) by { };
            assert(main[idx + k] == sub[k]);
        }
    };

    assert(main.subrange(idx, idx + len) =~= sub.subrange(0, len)) by {
        assert(main.subrange(idx, idx + len).len() == sub.subrange(0, len).len());
        assert forall|k: int| 0 <= k < main.subrange(idx, idx + len).len()
            implies main.subrange(idx, idx + len)[k] == sub.subrange(0, len)[k] by {
            assert(main.subrange(idx, idx + len)[k] == sub.subrange(0, len)[k]);
        };
        assert(main.subrange(idx, idx + len) =~= sub.subrange(0, len));
    };
}

// Complete the lemma function below
proof fn lemma_vec_view_subrange_index_equiv_i32(
    main: &Vec<i32>,
    sub: &Vec<i32>,
    idx: usize,
    i: usize,
    k: int,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn is_sub_list_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, (idx as int + sub@.len() as int)) =~= sub@),
{
    let mut i = 0;
    while i < sub.len()
        // Fill in loop invariants here
    {
        if (main[idx + i] != sub[i]) {
            // Fill in a block of assertions here to complete the proof;
            return false;
        }

        // Fill in a block of assertions here to complete the proof;

        i += 1;
    }

    assert(main@.subrange(idx as int, (idx as int + sub@.len() as int)) == sub@) by {
        let len = sub@.len() as int;

        lemma_subrange_eq_from_pointwise::<i32>(main@, sub@, idx as int, len);

        assert(main@.subrange(idx as int, (idx as int + len)) =~= sub@.subrange(0, len));
        assert(sub@.subrange(0, len) =~= sub@) by {
            assert(sub@.subrange(0, len).len() == len);
            assert(sub@.len() == len);
            assert(sub@.subrange(0, len) =~= sub@);
        };
        assert(main@.subrange(idx as int, (idx as int + len)) =~= sub@);
    };
    true
}

#[verifier::exec_allows_no_decreases_clause]
fn is_sub_list(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
    requires
        sub.len() <= main.len(),
    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
{
    if sub.len() > main.len() {
        return false;
    }
    let mut index = 0;
    while index <= (main.len() - sub.len())
        // Fill in loop invariants here
    {
        if (is_sub_list_at_index(&main, &sub, index)) {
            // Fill in a block of assertions here to complete the proof;
            return true;
        }
        index += 1;
    }
    false
}

} // verus!