use vstd::prelude::*;
fn main() {
}

verus! {
use vstd::assert_seqs_equal;

// Complete the lemma function below
proof fn lemma_seq_push_extends_subrange<T>(s: Seq<T>, a: T, start: int, end_: int)
   

proof fn lemma_seq_ext_eq_trans<A>(s1: Seq<A>, s2: Seq<A>, s3: Seq<A>)
    requires
        s1 =~= s2,
        s2 =~= s3,
    ensures
        s1 =~= s3,
{
    assert_seqs_equal!(s1, s3, i => {
        assert(s1.index(i) == s2.index(i));
        assert(s2.index(i) == s3.index(i));
    });
}

#[verifier::exec_allows_no_decreases_clause]
fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        new_list@ == list@.subrange((n as int), (list@.len() as int)).add(list@.subrange(0, (n as int))),
{
    let mut new_list = Vec::new();

    assert(new_list@ == Seq::<i32>::empty()) by {
        assert(new_list@ =~= Seq::<i32>::empty()) by {
            assert_seqs_equal!(new_list@, Seq::<i32>::empty(), i => { });
        }
    }
    assert(new_list@.len() == 0);

    let mut index = n;
    while index < list.len()
        invariant
            n <= index <= list.len(),
            list@.subrange((n as int), (index as int)) =~= new_list@,
    {
        let prev_index = index;

        assert(list@.subrange((n as int), (prev_index as int)) =~= new_list@);

        new_list.push(list[index]);
        index += 1;

        assert(new_list@ == list@.subrange((n as int), (prev_index as int)).push(list@.index((prev_index as int))));

        assert(list@.subrange((n as int), (prev_index as int) + 1) =~= new_list@) by {
            assert(list@.subrange((n as int), (prev_index as int) + 1)
                == list@.subrange((n as int), (prev_index as int)).push(list@.index((prev_index as int)))) by
            {
                let s = list@;
                let start = n as int;
                let end = prev_index as int;
                assert_seqs_equal!(s.subrange(start, end + 1), s.subrange(start, end).push(s[end]));
            }
        }
    }

    // Fill in a block of assertions here to complete the proof;

    let mut index = 0;
    while index < n
        invariant
            0 < n < list@.len(),
            0 <= index <= n,
            new_list@ =~= list@.subrange((n as int), (list@.len() as int)).add(
                list@.subrange(0, (index as int)),
            ),
    {
        assert(index < list.len()) by {
            assert(n < list@.len());
            assert(index < n);
        }

        let prev_index = index;

        assert(new_list@ =~= list@.subrange((n as int), (list@.len() as int)).add(list@.subrange(0, (prev_index as int))));

        new_list.push(list[index]);
        index += 1;

        assert(new_list@ == list@.subrange((n as int), (list@.len() as int)).add(list@.subrange(0, (prev_index as int))).push(list@.index((prev_index as int))));

        assert(list@.subrange(0, (prev_index as int) + 1) == list@.subrange(0, (prev_index as int)).push(list@.index((prev_index as int)))) by {
             let s = list@;
             let end = prev_index as int;
             assert_seqs_equal!(s.subrange(0, end + 1), s.subrange(0, end).push(s[end]));
        }

        assert(list@.subrange((n as int), (list@.len() as int)).add(list@.subrange(0, (prev_index as int))).push(list@.index((prev_index as int)))
            == list@.subrange((n as int), (list@.len() as int)).add(list@.subrange(0, (prev_index as int)).push(list@.index((prev_index as int))))) by
        {
            let s1 = list@.subrange((n as int), (list@.len() as int));
            let s2 = list@.subrange(0, (prev_index as int));
            let val = list@.index((prev_index as int));
            assert_seqs_equal!(s1.add(s2).push(val), s1.add(s2.push(val)));
        }

        assert(list@.subrange((n as int), (list@.len() as int)).add(list@.subrange(0, (prev_index as int)).push(list@.index((prev_index as int))))
            == list@.subrange((n as int), (list@.len() as int)).add(list@.subrange(0, (prev_index as int) + 1))) by
        {
            assert(list@.subrange(0, (prev_index as int) + 1)
                == list@.subrange(0, (prev_index as int)).push(list@.index((prev_index as int))));
        }

        assert(new_list@ =~= list@.subrange((n as int), (list@.len() as int)).add(
            list@.subrange(0, (index as int)),
        ));
    }

    assert(new_list@ == list@.subrange((n as int), (list@.len() as int)).add(list@.subrange(0, (n as int)))) by {
        assert(new_list@ =~= list@.subrange((n as int), (list@.len() as int)).add(list@.subrange(0, (n as int))));

        assert_seqs_equal!(new_list@, list@.subrange((n as int), (list@.len() as int)).add(list@.subrange(0, (n as int))), i => {
            assert(new_list@.index(i) == list@.subrange((n as int), (list@.len() as int)).add(list@.subrange(0, (n as int))).index(i));
        });
    }

    new_list
}

}