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

// Complete the lemma function below
proof fn lemma_subrange_eq_from_pointwise<T>(
    main: Seq<T>,
    sub: Seq<T>,
    idx: int,
    len: int,
)
   

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
            assert(exists|k: int, l: int|
                0 <= k <= (main.len() - sub.len()) && l == k + sub.len()
                    && (#[trigger](main@.subrange(k, l))) =~= sub@
            ) by {
                let k = index as int;
                let l = k + sub.len() as int;
                assert(main@.subrange(k, l) =~= sub@);
            };
            return true;
        }
        index += 1;
    }
    false
}

} // verus!