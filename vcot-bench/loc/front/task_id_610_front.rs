use vstd::prelude::*;
fn main() {
}

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, (k - 1) as int).add(
            list@.subrange(k as int, (list.len() as int)),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    while index < (k - 1)
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof;
        let ghost old = new_list@;
        let a = list[index];
        new_list.push(a);
        assert(new_list@ == old.push(a));
        assert(old == list@.subrange(0, (index as int)));
        assert(list@.subrange(0, (index as int)).push(list@[(index as int)]) == list@.subrange(0, (index as int) + 1));
        index += 1;
    }

    assert(new_list@ == list@.subrange(0, (k - 1) as int));

    let mut index = k;
    while index < list.len()
        invariant
            k <= index <= list.len(),
            0 < k < list@.len(),
            new_list@ =~= list@.subrange(0 as int, (k - 1) as int).add(
                list@.subrange(k as int, (index as int)),
            ),
    {
        // Fill in a block of assertions here to complete the proof;
        let ghost old = new_list@;
        let a = list[index];
        new_list.push(a);
        assert(new_list@ == old.push(a));

        proof {
            assert(old == list@.subrange(0 as int, (k - 1) as int).add(list@.subrange(k as int, (index as int))));

            let left = list@.subrange(0 as int, (k - 1) as int);
            let mid = list@.subrange(k as int, (index as int));
            let right = list@.subrange(k as int, ((index + 1) as int));

            assert(old == left.add(mid));
            assert(new_list@ == left.add(mid).push(a));

            assert(mid.push(a) =~= right) by {
                assert(mid.len() == (index as int) - (k as int));
                assert(right.len() == ((index + 1) as int) - (k as int));
                
                assert forall|i: int| 0 <= i < mid.push(a).len() implies mid.push(a)[i] == right[i] by {
                    assert(a == list@[index as int]);
                    if i < mid.len() {
                        assert(mid.push(a)[i] == mid[i]);
                        assert(mid[i] == list@[(k as int) + i]);
                        assert(right[i] == list@[(k as int) + i]);
                    } else {
                        assert(i == mid.len());
                        assert(mid.push(a)[i] == a);
                        assert(right[i] == list@[(k as int) + i]);
                    }
                }
            }
            assert(new_list@ == left.add(right));
        }

        index += 1;
    }

    assert(new_list@ == list@.subrange(0, (k - 1) as int).add(
        list@.subrange(k as int, (list.len() as int)),
    ));

    new_list
}

}