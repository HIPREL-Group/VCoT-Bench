use vstd::prelude::*;
fn main() {
}

verus! {

proof fn lemma_vec_push_view_maintains_subrange<T>(
    v_before: Seq<T>,
    a: T,
    base: Seq<T>,
    i: int,
)
    requires
        0 <= i < base.len(),
        v_before == base.subrange(0, i),
        a == base[i],
    ensures
        v_before.push(a) == base.subrange(0, i + 1),
{
    let v_after = v_before.push(a);

    assert(v_after.len() == v_before.len() + 1);
    assert(v_before.len() == i) by {
        assert(v_before.len() == base.subrange(0, i).len());
        assert(base.subrange(0, i).len() == i - 0);
    }
    assert(v_after.len() == i + 1);

    assert(v_after == base.subrange(0, i + 1)) by {
        assert(v_after.len() == base.subrange(0, i + 1).len()) by {
            assert(base.subrange(0, i + 1).len() == (i + 1) - 0);
        }

        assert forall|k: int| 0 <= k < v_after.len() implies v_after.index(k) == base.subrange(0, i + 1).index(k) by {
            assume(0 <= k < v_after.len());

            if k < i {
                assert(v_after.index(k) == v_before.index(k));
                assert(v_before.index(k) == base.subrange(0, i).index(k)) by {
                    assert(v_before == base.subrange(0, i));
                }
                assert(base.subrange(0, i).index(k) == base.index(k));
                assert(base.subrange(0, i + 1).index(k) == base.index(k));
            } else {
                assert(v_after.index(k) == a);
                assert(base.subrange(0, i + 1).index(k) == base.index(k));
            }
        };

        assert(v_after =~= base.subrange(0, i + 1));
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn split_array(list: &Vec<i32>, l: usize) -> (new_list: (Vec<i32>, Vec<i32>))
    requires
        list@.len() > 0,
        0 < l < list@.len(),
    ensures
        new_list.0@ == list@.subrange(0, (l as int)),
        new_list.1@ == list@.subrange((l as int), (list.len() as int)),
{
    let mut part1: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < l
        invariant
            0 < l < list@.len(),
            0 <= index <= l,
            part1@ =~= list@.subrange(0, (index as int)),
    {
        let ghost part1_before = part1@;
        let ghost idx_i: int = (index as int);
        // Fill in a block of assertions here to complete the proof;

        part1.push(list[index]);

        let ghost pushed = part1@;

        assert(pushed == list@.subrange(0, idx_i + 1)) by {
            assert(list@.subrange(0, idx_i + 1).len() == idx_i + 1) by {
                assert(list@.subrange(0, idx_i + 1).len() == (idx_i + 1) - 0);
            }
            assert(pushed.len() == idx_i + 1) by {
                assert(part1_before.len() == idx_i) by {
                    assert(part1_before.len() == list@.subrange(0, idx_i).len());
                    assert(list@.subrange(0, idx_i).len() == idx_i - 0);
                }
                assert(pushed.len() == part1_before.len() + 1);
            }

            assert forall|k: int| 0 <= k < pushed.len() implies pushed.index(k) == list@.subrange(0, idx_i + 1).index(k) by {
                if k < idx_i {
                    assert(pushed.index(k) == part1_before.index(k));
                    assert(part1_before.index(k) == list@.subrange(0, idx_i).index(k));
                    assert(list@.subrange(0, idx_i).index(k) == list@.index(k));
                    assert(list@.subrange(0, idx_i + 1).index(k) == list@.index(k));
                } else {
                    assert(pushed.index(k) == list@[idx_i]);
                    assert(list@.subrange(0, idx_i + 1).index(k) == list@.index(k));
                    assert(list@.index(k) == list@[idx_i]);
                }
            };
            assert(pushed =~= list@.subrange(0, idx_i + 1));
        }

        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }
    let mut part2: Vec<i32> = Vec::new();
    index = l;
    while index < list.len()
        invariant
            l <= index <= list.len(),
            part2@ =~= list@.subrange((l as int), (index as int)),
    {
        let ghost part2_before = part2@;
        let ghost start: int = (l as int);
        let ghost idx_i: int = (index as int);
        // Fill in a block of assertions here to complete the proof;

        part2.push(list[index]);

        let ghost pushed = part2@;

        assert(pushed == list@.subrange(start, idx_i + 1)) by {
            assert(list@.subrange(start, idx_i + 1).len() == (idx_i + 1) - start);
            assert(part2_before.len() == idx_i - start);
            assert(pushed.len() == part2_before.len() + 1);
            assert(pushed.len() == (idx_i + 1) - start);

            assert forall|k: int| 0 <= k < pushed.len() implies pushed.index(k) == list@.subrange(start, idx_i + 1).index(k) by {
                if k < (idx_i - start) {
                    assert(pushed.index(k) == part2_before.index(k));
                    assert(part2_before.index(k) == list@.subrange(start, idx_i).index(k));
                    assert(list@.subrange(start, idx_i).index(k) == list@.index(start + k));
                    assert(list@.subrange(start, idx_i + 1).index(k) == list@.index(start + k));
                } else {
                    assert(pushed.index(k) == list@[idx_i]);
                    assert(list@.subrange(start, idx_i + 1).index(k) == list@.index(start + k));
                }
            };
            assert(pushed =~= list@.subrange(start, idx_i + 1));
        }

        index += 1;

        assert(part2@ =~= list@.subrange((l as int), (index as int)));
    }

    assert(part1@ =~= list@.subrange(0, (l as int)));
    assert(part2@ =~= list@.subrange((l as int), (list.len() as int)));

    (part1, part2)
}

}