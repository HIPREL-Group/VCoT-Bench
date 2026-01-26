use vstd::prelude::*;
fn main() {
}

verus! {

spec fn rotation_split(len: usize, n: usize) -> int {
    len - (n % len)
}

// Complete the lemma function below
proof fn lemma_seq_push_extends_prefix<A>(s: Seq<A>, a: A)
    

// Complete the lemma function below
proof fn lemma_subrange_index_shift<A>(s: Seq<A>, start: int, end: int, i: int)
   

// Complete the lemma function below
proof fn lemma_subrange_len<A>(s: Seq<A>, start: int, end: int)
   

proof fn lemma_seq_ext_eq_from_pointwise<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        s1.len() == s2.len(),
        forall|i: int| 0 <= i < s1.len() ==> s1.index(i) == s2.index(i),
    ensures
        s1 =~= s2
{
    assert(s1 =~= s2);
}

// Complete the lemma function below
proof fn lemma_seq_add_push_right<A>(right: Seq<A>, left: Seq<A>, a: A)
    

#[verifier::exec_allows_no_decreases_clause]
fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)
    requires
        list.len() > 0,
    ensures
        new_list.len() == list.len(),
        new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(
            list@.subrange(0, rotation_split(list.len(), n) as int),
        ),
{
    let rotation = n % list.len();
    let split_index = list.len() - rotation;

    let mut new_list = Vec::with_capacity(list.len());

    let mut index = split_index;

    while index < list.len()
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof

        new_list.push(list[index]);
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }

    index = 0;
    while index < split_index
        // Fill in loop invariants here
    {
        proof {
            let pre_new = new_list@;
            let pre_i = index;

            assert(pre_new =~=
                list@.subrange(split_index as int, list@.len() as int).add(
                    list@.subrange(0, pre_i as int),
                )
            );

            let elem = list@[pre_i as int];

            let right = list@.subrange(split_index as int, list@.len() as int);
            let left_pre = list@.subrange(0, pre_i as int);
            let left_next = list@.subrange(0, (pre_i + 1) as int);

            assert(left_next == left_pre.push(elem)) by {
                assert forall|j: int|
                    0 <= j < (pre_i + 1) implies left_next.index(j) == left_pre.push(elem).index(j)
                by {
                    if j < pre_i as int {
                        lemma_subrange_index_shift(list@, 0, (pre_i + 1) as int, j);
                        lemma_subrange_index_shift(list@, 0, pre_i as int, j);
                        assert(left_next.index(j) == list@.index(j));
                        assert(left_pre.index(j) == list@.index(j));
                        assert(left_pre.push(elem).index(j) == left_pre.index(j));
                    } else {
                        lemma_subrange_index_shift(list@, 0, (pre_i + 1) as int, j);
                        assert(left_next.index(j) == list@.index(j));
                        assert(left_pre.push(elem).index(j) == elem);
                    }
                }
                lemma_subrange_len(list@, 0, (pre_i + 1) as int);
                lemma_subrange_len(list@, 0, pre_i as int);
                assert(left_next.len() == left_pre.push(elem).len());
                lemma_seq_ext_eq_from_pointwise(left_next, left_pre.push(elem));
                assert(left_next == left_pre.push(elem));
            }

            assert(right.add(left_next) == right.add(left_pre.push(elem)));

            assert(pre_new.push(elem) =~= right.add(left_next)) by {
                assert(pre_new.push(elem) =~= right.add(left_pre).push(elem));
                lemma_seq_add_push_right(right, left_pre, elem);
                assert(right.add(left_pre).push(elem) == right.add(left_pre.push(elem)));
                assert(right.add(left_pre.push(elem)) == right.add(left_next));
            }
        }

        new_list.push(list[index]);
        index += 1;

        proof {
            assert(new_list@ =~= list@.subrange(split_index as int, list@.len() as int).add(
                list@.subrange(0, index as int),
            ));
        }
    }

    assert(split_index as int == rotation_split(list.len(), n));

    assert(new_list@ =~= list@.subrange(split_index as int, list@.len() as int).add(
        list@.subrange(0, split_index as int),
    ));
    new_list
}

} // verus!