use vstd::prelude::*;

fn main() {
}

verus! {

spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> int
    decreases s1.len(), s2.len(), s3.len(),
{
    if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
        0
    } else {
        count_identical(s1.drop_last(), s2.drop_last(), s3.drop_last()) + if (s1.last() == s2.last()
            && s2.last() == s3.last()) {
            (1 as int)
        } else {
            (0 as int)
        }
    }
}

proof fn lemma_subrange_drop_last<A>(s: Seq<A>, i: int)
    requires
        1 <= i,
        i <= s.len(),
    ensures
        s.subrange(0, i - 1) == s.subrange(0, i).drop_last(),
{
    assert(s.subrange(0, i).drop_last() == s.subrange(0, i).subrange(0, s.subrange(0, i).len() - 1));
    assert(s.subrange(0, i).subrange(0, s.subrange(0, i).len() - 1) == s.subrange(0, i - 1));
}

proof fn lemma_subrange_all<A>(s: Seq<A>, i: int)
    requires
        i == s.len(),
    ensures
        s == s.subrange(0, i),
{
    assert(s.subrange(0, s.len() as int) == s);
}

proof fn lemma_count_identical_step(
    s1: Seq<i32>,
    s2: Seq<i32>,
    s3: Seq<i32>,
    i: int,
)
    requires
        1 <= i,
        i <= s1.len(),
        s1.len() == s2.len(),
        s2.len() == s3.len(),
    ensures
        count_identical(s1.subrange(0, i), s2.subrange(0, i), s3.subrange(0, i))
            == count_identical(s1.subrange(0, i - 1), s2.subrange(0, i - 1), s3.subrange(0, i - 1))
                + if s1[i - 1] == s2[i - 1] && s2[i - 1] == s3[i - 1] { 1int } else { 0int },
{
    let t1 = s1.subrange(0, i);
    let t2 = s2.subrange(0, i);
    let t3 = s3.subrange(0, i);

    lemma_subrange_drop_last(s1, i);
    lemma_subrange_drop_last(s2, i);
    lemma_subrange_drop_last(s3, i);

    assert(t1.drop_last() == s1.subrange(0, i - 1));
    assert(t2.drop_last() == s2.subrange(0, i - 1));
    assert(t3.drop_last() == s3.subrange(0, i - 1));

    assert(t1.last() == s1[i - 1]);
    assert(t2.last() == s2[i - 1]);
    assert(t3.last() == s3[i - 1]);

    assert(
        count_identical(t1, t2, t3)
            == count_identical(t1.drop_last(), t2.drop_last(), t3.drop_last())
                + (if (t1.last() == t2.last() && t2.last() == t3.last()) { 1int } else { 0int })
    );

    assert(
        (if (t1.last() == t2.last() && t2.last() == t3.last()) { 1int } else { 0int })
            == (if s1[i - 1] == s2[i - 1] && s2[i - 1] == s3[i - 1] { 1int } else { 0int })
    );

    assert(
        count_identical(t1, t2, t3)
            == count_identical(s1.subrange(0, i - 1), s2.subrange(0, i - 1), s3.subrange(0, i - 1))
                + (if s1[i - 1] == s2[i - 1] && s2[i - 1] == s3[i - 1] { 1int } else { 0int })
    );
}

#[verifier::exec_allows_no_decreases_clause]
fn count_identical_position(arr1: &Vec<i32>, arr2: &Vec<i32>, arr3: &Vec<i32>) -> (count: usize)
    requires
        arr1.len() == arr2.len() && arr2.len() == arr3.len(),
    ensures
        0 <= count <= arr1.len(),
        count_identical(arr1@, arr2@, arr3@) == count,
{
    let mut count = 0;
    let mut index = 0;
    while index < arr1.len()
        // Fill in loop invariants here
    {
        let old_index = index;
        let old_count = count;

        if arr1[index] == arr2[index] && arr2[index] == arr3[index] {
            count += 1;
        }
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof

    count
}

}