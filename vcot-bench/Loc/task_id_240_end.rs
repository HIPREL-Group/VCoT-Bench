use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_subrange_add_whole<A>(s: Seq<A>, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        s.subrange(0, n).add(s.subrange(n, s.len() as int)) == s,
{
    assert(forall|i: int| 0 <= i < s.len() ==>
        s.subrange(0, n).add(s.subrange(n, s.len() as int)).index(i) == s.index(i)) by {
        assert forall|i: int| 0 <= i < s.len() implies
            s.subrange(0, n).add(s.subrange(n, s.len() as int)).index(i) == s.index(i)
        by {
            if i < n {
                assert(s.subrange(0, n).add(s.subrange(n, s.len() as int)).index(i)
                    == s.subrange(0, n).index(i));
                assert(s.subrange(0, n).index(i) == s.index(i));
            } else {
                let j = i - n;
                assert(s.subrange(0, n).add(s.subrange(n, s.len() as int)).index(i)
                    == s.subrange(n, s.len() as int).index(j));
                assert(s.subrange(n, s.len() as int).index(j) == s.index(n + j));
                assert(n + j == i);
            }
        }
    }

    assert(s.subrange(0, n).add(s.subrange(n, s.len() as int)) == s) by {
        assert(s.subrange(0, n).add(s.subrange(n, s.len() as int)) =~= s);
    }
}

proof fn lemma_seq_add_append_one<A>(s1: Seq<A>, s2: Seq<A>, a: A)
    ensures
        s1.add(s2).push(a) == s1.add(s2.push(a)),
{
    let left = s1.add(s2).push(a);
    let right = s1.add(s2.push(a));

    assert forall|i: int| 0 <= i < left.len() implies left.index(i) == right.index(i) by {
        if i < s1.len() {
            assert(left.index(i) == s1.add(s2).index(i));
            assert(s1.add(s2).index(i) == s1.index(i));
            assert(right.index(i) == s1.add(s2.push(a)).index(i));
            assert(s1.add(s2.push(a)).index(i) == s1.index(i));
        } else if i < s1.len() + s2.len() {
            let j = i - s1.len();
            assert(left.index(i) == s1.add(s2).index(i));
            assert(s1.add(s2).index(i) == s2.index(j));
            assert(right.index(i) == s1.add(s2.push(a)).index(i));
            assert(s1.add(s2.push(a)).index(i) == s2.push(a).index(j));
            assert(s2.push(a).index(j) == s2.index(j));
        } else {
            assert(left.index(i) == a);
            assert(right.index(i) == s1.add(s2.push(a)).index(i));
            assert(s1.add(s2.push(a)).index(i) == s2.push(a).index(i - s1.len()));
            assert(i - s1.len() == s2.len());
            assert(s2.push(a).index(s2.len() as int) == a);
        }
    }

    assert(left =~= right);
    assert(left == right);
}

proof fn lemma_subrange_all<A>(s: Seq<A>)
    ensures
        s.subrange(0, s.len() as int) == s,
{
    assert(s.subrange(0, s.len() as int) =~= s);
}

#[verifier::exec_allows_no_decreases_clause]
fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
    requires
        first.len() > 0,
    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
{
    let mut replaced_list = Vec::new();
    let first_end = first.len() - 1;
    let mut index = 0;

    proof {
        lemma_subrange_add_whole(first@, first_end as int);
    }

    while index < first_end
        invariant
            first_end == first.len() - 1,
            0 <= index <= first_end,
            replaced_list@ =~= first@.subrange(0, index as int),
    {
        replaced_list.push(first[index]);
        index += 1;

        proof {
            assert(replaced_list@ =~= first@.subrange(0, index as int));
        }
    }
    index = 0;

    proof {
        assert(replaced_list@ =~= first@.subrange(0, first_end as int));
        assert(replaced_list@ =~= first@.subrange(0, first.len() as int - 1));
        assert(replaced_list@ =~=
            first@.subrange(0, first.len() as int - 1).add(second@.subrange(0, 0)));
    }

    while index < second.len()
        invariant
            0 <= index <= second.len(),
            replaced_list@ =~= first@.subrange(0, first.len() as int - 1).add(
                second@.subrange(0, index as int),
            ),
    {
        replaced_list.push(second[index]);
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof;

    replaced_list
}

}