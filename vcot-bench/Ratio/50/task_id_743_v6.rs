use vstd::prelude::*;
fn main() {
}

verus! {

spec fn rotation_split(len: usize, n: usize) -> int {
    len - (n % len)
}

// Complete the lemma function below
proof fn lemma_seq_push_extends_prefix<A>(s: Seq<A>, a: A)
    

proof fn lemma_subrange_index_shift<A>(s: Seq<A>, start: int, end: int, i: int)
    requires
        0 <= start <= end <= s.len(),
        0 <= i < end - start,
    ensures
        s.subrange(start, end).index(i) == s.index(start + i)
{
    assert(s.subrange(start, end).index(i) == s.index(start + i));
}

proof fn lemma_subrange_len<A>(s: Seq<A>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        s.subrange(start, end).len() == end - start
{
    assert(s.subrange(start, end).len() == end - start);
}

proof fn lemma_seq_ext_eq_from_pointwise<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        s1.len() == s2.len(),
        forall|i: int| 0 <= i < s1.len() ==> s1.index(i) == s2.index(i),
    ensures
        s1 =~= s2
{
    assert(s1 =~= s2);
}

proof fn lemma_seq_add_push_right<A>(right: Seq<A>, left: Seq<A>, a: A)
    ensures
        right.add(left).push(a) == right.add(left.push(a))
{
    let s1 = right.add(left).push(a);
    let s2 = right.add(left.push(a));

    assert(s1.len() == s2.len()) by {
        assert(s1.len() == right.len() + left.len() + 1);
        assert(s2.len() == right.len() + (left.len() + 1));
    }

    assert forall|i: int| 0 <= i < s1.len() implies s1.index(i) == s2.index(i) by {
        if i < right.len() {
            assert(s1.index(i) == right.index(i));
            assert(s2.index(i) == right.index(i));
        } else if i < right.len() + left.len() {
            let j = i - right.len();
            assert(0 <= j < left.len());
            assert(s1.index(i) == left.index(j));
            assert(s2.index(i) == left.push(a).index(j));
            assert(left.push(a).index(j) == left.index(j));
        } else {
            assert(i == right.len() + left.len());
            assert(s1.index(i) == a);
            assert(s2.index(i) == left.push(a).index(left.len() as int));
            assert(left.push(a).index(left.len() as int) == a);
        }
    }

    lemma_seq_ext_eq_from_pointwise(s1, s2);
    assert(right.add(left).push(a) == right.add(left.push(a)));
}

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
        invariant
            0 <= split_index <= list@.len(),
            0 <= index <= split_index,
            new_list@ =~= list@.subrange(split_index as int, list@.len() as int).add(
                list@.subrange(0, index as int),
            ),
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

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof;
    new_list
}

} // verus!