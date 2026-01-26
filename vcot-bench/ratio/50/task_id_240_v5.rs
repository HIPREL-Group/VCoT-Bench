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

// Complete the lemma function below
proof fn lemma_seq_add_append_one<A>(s1: Seq<A>, s2: Seq<A>, a: A)
    

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

    // Fill in a block of assertions here to complete the proof

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
        // Fill in loop invariants here
    {
        replaced_list.push(second[index]);
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof;

    replaced_list
}

}