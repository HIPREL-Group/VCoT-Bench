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
        invariant
            0 <= idx <= (main.len() - sub.len()),
            0 <= i <= sub.len(),
            0 <= idx + i <= main.len(),
            forall|k: int| 0 <= k < i ==> main[(idx as int) + k] == sub[k],
            forall|k: int|
                0 <= k < i ==> (main@.subrange(idx as int, (idx as int + k)) =~= sub@.subrange(0, k)),
    {
        if (main[idx + i] != sub[i]) {
            assert(exists|k: int| 0 <= k < sub@.len() && main[(idx as int) + k] != sub[k]) by {
                let k = i as int;
                assert(main[(idx as int) + k] == main[(idx + i) as int]);
                assert(sub[k] == sub[i as int]);
                assert(main[(idx + i) as int] != sub[i as int]);
                assert(main[(idx as int) + k] != sub[k]);
            };

            assert(!(main@.subrange(idx as int, (idx as int + sub@.len() as int)) =~= sub@)) by {
                let s = main@.subrange(idx as int, (idx as int + sub@.len() as int));
                assert(s.len() == sub@.len()) by { };

                if s =~= sub@ {
                    lemma_subrange_ext_eq_implies_index_eq::<i32>(s, sub@, i as int);
                    lemma_vec_view_subrange_index_equiv_i32(main, sub, idx, i, i as int);
                    assert(main[(idx + i) as int] == sub[i as int]);
                    assert(false);
                }
            };

            assert(main@.subrange(idx as int, (idx as int + sub@.len() as int)) != sub@);
            return false;
        }

        assert(main[(idx + i) as int] == sub[i as int]);

        assert(forall|k: int|
            0 <= k < (i + 1) ==> (main@.subrange(idx as int, (idx as int + k)) =~= sub@.subrange(0, k))
        ) by {
            assert forall|k: int| 0 <= k < (i + 1) implies
                (main@.subrange(idx as int, (idx as int + k)) =~= sub@.subrange(0, k))
            by {
                if k < i as int {
                    assert(main@.subrange(idx as int, (idx as int + k)) =~= sub@.subrange(0, k));
                } else {
                    assert(k == i as int);

                    assert(forall|t: int| 0 <= t < k ==> main@[(idx as int) + t] == sub@[t]) by {
                        assert forall|t: int| 0 <= t < k implies main@[(idx as int) + t] == sub@[t] by {
                            assert(main[(idx as int) + t] == sub[t]);
                            assert(main@[(idx as int) + t] == main[(idx as int) + t]);
                            assert(sub@[t] == sub[t]);
                            assert(main@[(idx as int) + t] == sub@[t]);
                        }
                    };

                    lemma_subrange_eq_from_pointwise::<i32>(main@, sub@, idx as int, k);

                    assert(main@.subrange(idx as int, (idx as int) + k) =~= sub@.subrange(0, k));
                    assert(main@.subrange(idx as int, (idx + k) as int) =~= sub@.subrange(0, k));
                }
            }
        };

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
        invariant
            sub.len() <= main.len(),
            0 <= index <= (main.len() - sub.len()) + 1,
            forall|k: int, l: int|
                (0 <= k < index) && l == k + sub.len() ==> (#[trigger] (main@.subrange(k, l))
                    != sub@),
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