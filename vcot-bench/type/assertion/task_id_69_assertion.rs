use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_subrange_ext_eq_implies_index_eq<T>(
    s1: Seq<T>,
    s2: Seq<T>,
    i: int,
)
    requires
        s1.len() == s2.len(),
        0 <= i < s1.len(),
        s1 =~= s2,
    ensures
        s1[i] == s2[i],
{
    assert forall|k: int| 0 <= k < s1.len() implies s1[k] == s2[k] by { };
}

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

proof fn lemma_vec_view_subrange_index_equiv_i32(
    main: &Vec<i32>,
    sub: &Vec<i32>,
    idx: usize,
    i: usize,
    k: int,
)
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
        i < sub.len(),
        k == i as int,
    ensures
        main@.subrange(idx as int, (idx as int + sub@.len() as int))[k] == main[(idx + i) as int],
        sub@[k] == sub[i as int],
{
    let s = main@.subrange(idx as int, (idx as int + sub@.len() as int));
    assert(s[k] == main@[(idx as int) + k]) by { };
    assert(main@[(idx as int) + k] == main[(idx + i) as int]) by { };
    assert(sub@[k] == sub[i as int]) by { };
}

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
        invariant
            0 <= idx <= (main.len() - sub.len()),
            0 <= i <= sub.len(),
            0 <= idx + i <= main.len(),
            forall|k: int| 0 <= k < i ==> main[(idx as int) + k] == sub[k],
            forall|k: int|
                0 <= k < i ==> (main@.subrange(idx as int, (idx as int + k)) =~= sub@.subrange(0, k)),
    {
        if (main[idx + i] != sub[i]) {
            // Fill in a block of assertions here to complete the proof;
            return false;
        }

        // Fill in a block of assertions here to complete the proof;

        i += 1;
    }

    // Fill in a block of assertions here to complete the proof;
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
        invariant
            sub.len() <= main.len(),
            0 <= index <= (main.len() - sub.len()) + 1,
            forall|k: int, l: int|
                (0 <= k < index) && l == k + sub.len() ==> (#[trigger] (main@.subrange(k, l))
                    != sub@),
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