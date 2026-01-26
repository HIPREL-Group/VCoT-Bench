use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_extend_outer_invariant_on_i_increment(i: int, list1: &Vec<i32>, list2: &Vec<i32>)
   

proof fn lemma_inner_invariant_preserved_after_j_increment(
    i: int,
    j_old: int,
    list1: &Vec<i32>,
    list2: &Vec<i32>,
)
    requires
        0 <= i < list1.len(),
        0 <= j_old < list2.len(),
        forall|k: int| 0 <= k < j_old ==> (list1[i] != list2[k]),
        list1[i] != list2[j_old],
    ensures
        forall|k: int| 0 <= k < j_old + 1 ==> (list1[i] != list2[k]),
{
    assert forall|k: int| 0 <= k < j_old + 1 ==> (list1[i] != list2[k]) by {
        if 0 <= k < j_old + 1 {
            if k < j_old {
                assert(list1[i] != list2[k]);
            } else {
                assert(list1[i] != list2[k]);
            }
        }
    }
}

proof fn lemma_no_common_element_from_forall_neq(
    list1: &Vec<i32>,
    list2: &Vec<i32>,
    i_end: int,
)
    requires
        i_end == list1.len(),
        forall|ii: int, jj: int|
            0 <= ii < i_end && 0 <= jj < list2.len() ==> (list1[ii] != list2[jj]),
    ensures
        !(exists|ii: int, jj: int|
            0 <= ii < list1.len() && 0 <= jj < list2.len() && (list1[ii] == list2[jj])),
{
    assert(!(exists|ii: int, jj: int|
        0 <= ii < list1.len() && 0 <= jj < list2.len() && (list1[ii] == list2[jj]))) by {
        if exists|ii: int, jj: int|
            0 <= ii < list1.len() && 0 <= jj < list2.len() && (list1[ii] == list2[jj]) {
            let (ii0, jj0) = choose|ii: int, jj: int|
                0 <= ii < list1.len() && 0 <= jj < list2.len() && (list1[ii] == list2[jj]);
            assert(list1[ii0] == list2[jj0]);

            assert(0 <= ii0 < i_end) by {
                assert(i_end == list1.len());
            };
            assert(list1[ii0] != list2[jj0]);

            assert(false);
        }
    };
}

#[verifier::exec_allows_no_decreases_clause]
fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
{
    let mut i = 0;
    while i < list1.len()
        invariant
            0 <= i <= list1.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < list2.len() ==> (list1[k] != list2[j]),
    {
        let mut j = 0;
        while j < list2.len()
            invariant
                0 <= i < list1.len(),
                0 <= j <= list2.len(),
                forall|k: int| 0 <= k < j ==> (list1[i as int] != list2[k]),
        {
            if list1[i] == list2[j] {
                assert(exists|ii: int, jj: int|
                    0 <= ii < list1.len() && 0 <= jj < list2.len() && (list1[ii] == list2[jj])) by {
                    assert(list1[i as int] == list2[j as int]);
                };
                return true;
            }

            let j_old = j;
            j += 1;

            assert(0 <= j_old < list2.len());
            assert(0 <= j <= list2.len());

            assert(list1[i as int] != list2[j_old as int]);

            assert(forall|k: int| 0 <= k < j ==> (list1[i as int] != list2[k])) by {
                lemma_inner_invariant_preserved_after_j_increment(
                    i as int,
                    j_old as int,
                    list1,
                    list2,
                );
            }
        }

        assert(forall|jj: int| 0 <= jj < list2.len() ==> (list1[i as int] != list2[jj])) by {
            assert forall|jj: int| 0 <= jj < list2.len() ==> (list1[i as int] != list2[jj]) by {
                if 0 <= jj < list2.len() {
                    assert(0 <= jj < j as int);
                    assert(list1[i as int] != list2[jj]);
                }
            }
        }

        assert(forall|k: int, j2: int| 0 <= k < i + 1 && 0 <= j2 < list2.len() ==> (list1[k] != list2[j2])) by {
            lemma_extend_outer_invariant_on_i_increment(i as int, list1, list2);
        }

        i += 1;
    }

    assert(!(exists|ii: int, jj: int|
        0 <= ii < list1.len() && 0 <= jj < list2.len() && (list1[ii] == list2[jj]))) by {
        assert forall|ii: int, jj: int|
            0 <= ii < list1.len() && 0 <= jj < list2.len() ==> list1[ii] != list2[jj] by {
            if 0 <= ii < list1.len() && 0 <= jj < list2.len() {
                assert(ii < i as int) by {
                    assert(i == list1.len() as int);
                };
                assert(list1[ii] != list2[jj]);
            }
        }

        lemma_no_common_element_from_forall_neq(list1, list2, i as int);
    };

    false
}

} // verus!