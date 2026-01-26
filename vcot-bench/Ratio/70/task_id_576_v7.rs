use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_subrange_eq_implies_all_index_eq<T>(
    s1: Seq<T>,
    s2: Seq<T>,
)
    

// Complete the lemma function below
proof fn lemma_subrange_append_point_i32(
    main: Seq<i32>,
    sub: Seq<i32>,
    idx: int,
    i: int,
)
   

proof fn lemma_extend_subrange_invariant_i32(
    main: Seq<i32>,
    sub: Seq<i32>,
    idx: int,
    i: int,
)
    requires
        0 <= i <= sub.len(),
        0 <= idx,
        idx + i <= main.len(),
        forall|k: int| 0 <= k < i ==> main[idx + k] == sub[k],
    ensures
        main.subrange(idx, idx + i) =~= sub.subrange(0, i),
{
    if i == 0 {
        assert(main.subrange(idx, idx) =~= sub.subrange(0, 0));
    } else {
        assert(main.subrange(idx, idx + i) =~= sub.subrange(0, i)) by {
            assert(forall|k: int| 0 <= k < i ==> main[idx + k] == sub[k]);
        };
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange((idx as int), ((idx as int) + sub@.len())) =~= sub@),
{
    let mut i = 0;
    while i < sub.len()
        // Fill in loop invariants here
    {
        if (main[idx + i] != sub[i]) {
            assert(exists|k: int| 0 <= k < i ==> main[idx + k] != sub[k]);
            assert(main@.subrange((idx as int), ((idx as int) + sub@.len())) != sub@);
            return false;
        }
        assert(main[((idx + i) as int)] == sub[(i as int)]);

        assert(main@.subrange((idx as int), ((idx as int) + (i as int))) =~= sub@.subrange(0, (i as int))) by {
            lemma_extend_subrange_invariant_i32(
                main@,
                sub@,
                (idx as int),
                (i as int),
            );
        };
        assert(main@.subrange((idx as int), ((idx as int) + ((i + 1) as int))) =~= sub@.subrange(0, ((i + 1) as int))) by {
            lemma_subrange_append_point_i32(
                main@,
                sub@,
                (idx as int),
                (i as int),
            );
        };
        i += 1;

        // Fill in a block of assertions here to complete the proof;
    }
    // Fill in a block of assertions here to complete the proof;
    true
}

#[verifier::exec_allows_no_decreases_clause]
fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
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
        if (sub_array_at_index(&main, &sub, index)) {
            return true;
        }

        // Fill in a block of assertions here to complete the proof;

        index += 1;
    }
    false
}

}