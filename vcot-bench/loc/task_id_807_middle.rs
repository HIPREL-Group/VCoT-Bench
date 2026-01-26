use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_take_drop_last_step<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.take(i + 1).drop_last() == s.take(i),
{
    assert(s.take((i + 1)).drop_last() =~= s.take(i)) by {
        reveal(Seq::take);
        reveal(Seq::drop_last);
    }
}

proof fn lemma_filter_push_keeps_last_u32(s: Seq<u32>, x: u32)
    ensures
        s.push(x).filter(|y: u32| y % 2 == 0)
        == if x % 2 == 0 { s.filter(|y: u32| y % 2 == 0).push(x) } else { s.filter(|y: u32| y % 2 == 0) },
{
    let p = |y: u32| y % 2 == 0;
    reveal(Seq::filter);
    reveal(Seq::last);
    reveal(Seq::drop_last);
    reveal(Seq::take);

    assert(s.push(x).last() == x);
    assert(s.push(x).drop_last() =~= s);

    assert(s.push(x).filter(p)
        == if x % 2 == 0 { s.filter(p).push(x) } else { s.filter(p) });
}

proof fn lemma_filter_push_even_u32(s: Seq<u32>, x: u32)
    requires
        x % 2 == 0,
    ensures
        s.push(x).filter(|y: u32| y % 2 == 0)
        == s.filter(|y: u32| y % 2 == 0).push(x),
{
    reveal(Seq::filter);
    assert(s.push(x).filter(|y: u32| y % 2 == 0)
        == if x % 2 == 0 { s.filter(|y: u32| y % 2 == 0).push(x) } else { s.filter(|y: u32| y % 2 == 0) }) by {
        lemma_filter_push_keeps_last_u32(s, x);
    }
}

proof fn lemma_filter_take_push_step_u32(s: Seq<u32>, i: int)
    requires
        0 <= i < s.len(),
        s.take(i) =~= s.take(i).filter(|x: u32| x % 2 == 0),
        s[i] % 2 == 0,
    ensures
        s.take(i + 1) =~= s.take(i + 1).filter(|x: u32| x % 2 == 0),
{
    reveal(Seq::filter);
    reveal(Seq::take);

    assert(s.take(i + 1) =~= s.take(i).push(s[i]));

    assert(s.take(i + 1).filter(|x: u32| x % 2 == 0)
        =~= s.take(i).push(s[i]).filter(|x: u32| x % 2 == 0));

    assert(s.take(i).push(s[i]).filter(|x: u32| x % 2 == 0)
        =~= s.take(i).filter(|x: u32| x % 2 == 0).push(s[i])) by {
        lemma_filter_push_even_u32(s.take(i), s[i]);
    }

    assert(s.take(i).push(s[i]) =~= s.take(i).filter(|x: u32| x % 2 == 0).push(s[i]));

    assert(s.take(i + 1) =~= s.take(i + 1).filter(|x: u32| x % 2 == 0));
}

proof fn lemma_filter_index_implies_pred_u32(s: Seq<u32>, j: int)
    requires
        0 <= j < s.filter(|x: u32| x % 2 == 0).len(),
    ensures
        s.filter(|x: u32| x % 2 == 0)[j] % 2 == 0,
{
    reveal(Seq::filter);
}

proof fn lemma_seq_eq_filter_all_satisfy_u32(s: Seq<u32>)
    requires
        s =~= s.filter(|x: u32| x % 2 == 0),
    ensures
        forall|k: int| 0 <= k < s.len() ==> (s[k] % 2 == 0),
{
    let p = |x: u32| x % 2 == 0;
    reveal(Seq::filter);

    assert(forall|k: int| 0 <= k < s.len() ==> p(s[k])) by {
        assert(forall|k: int| 0 <= k < s.len() ==> (#[trigger] s[k] == s.filter(p)[k])) by {
            assert(s == s.filter(p));
        };
        assert(forall|k: int| 0 <= k < s.len() ==> p(s.filter(p)[k])) by {
            assert(forall|k: int| 0 <= k < s.filter(p).len() ==> p(s.filter(p)[k])) by {
                assert(forall|k: int|
                    0 <= k < s.filter(p).len() ==> p(s.filter(p)[k])
                ) by { };
            };
            assert(s.len() == s.filter(p).len()) by {
                assert(s == s.filter(p));
            }
        };
    };
}

proof fn lemma_vec_view_take_len<A>(v: &Vec<A>)
    ensures
        v@ == v@.take(v.len() as int),
{
    assert(v@ =~= v@.take((v.len() as int))) by {
        reveal(Seq::take);
    }
}

proof fn lemma_vec_index_view_eq<A>(v: &Vec<A>)
    ensures
        forall|k: int| 0 <= k < v.len() ==> v[k] == v@[k],
{
    assert(forall|k: int| 0 <= k < v.len() ==> v[k] == v@[k]) by { }
}

#[verifier::exec_allows_no_decreases_clause]
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures
        if let Some(idx) = index {
            &&& arr@.take((idx as int)) == arr@.take((idx as int)).filter(|x: u32| x % 2 == 0)
            &&& arr[(idx as int)] % 2 != 0
        } else {
            forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
        },
{
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            arr@.take((index as int)) =~= arr@.take((index as int)).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 != 0) {
            return Some(index);
        }

        // Fill in a block of assertions here to complete the proof

        reveal(Seq::filter);

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }

    assert(arr@ == arr@.take((input_len as int))) by {
        assert(input_len == arr.len());
        lemma_vec_view_take_len(arr);
    }

    assert(forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)) by {
        assert(arr@.take((arr.len() as int)) =~= arr@.take((arr.len() as int)).filter(|x: u32| x % 2 == 0)) by {
            assert(arr@.take((index as int)) =~= arr@.take((index as int)).filter(|x: u32| x % 2 == 0));
            assert(index == arr.len());
        };

        assert(arr@ =~= arr@.filter(|x: u32| x % 2 == 0)) by {
            assert(arr@ == arr@.take((arr.len() as int)));
            assert(arr@.filter(|x: u32| x % 2 == 0) == arr@.take((arr.len() as int)).filter(|x: u32| x % 2 == 0));
        }

        lemma_seq_eq_filter_all_satisfy_u32(arr@);

        assert(forall|k: int| 0 <= k < arr.len() ==> (arr@[k] % 2 == 0)) by { };

        assert(forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)) by {
            lemma_vec_index_view_eq(arr);
        };
    };

    None
}

} // verus!