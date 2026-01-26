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

// Complete the lemma function below
proof fn lemma_subrange_drop_last<A>(s: Seq<A>, i: int)
   

// Complete the lemma function below
proof fn lemma_subrange_all<A>(s: Seq<A>, i: int)
   

// Complete the lemma function below
proof fn lemma_count_identical_step(
    s1: Seq<i32>,
    s2: Seq<i32>,
    s3: Seq<i32>,
    i: int,
)
   

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

        proof {
            lemma_subrange_drop_last(arr1@, (index as int));
            lemma_subrange_drop_last(arr2@, (index as int));
            lemma_subrange_drop_last(arr3@, (index as int));

            lemma_count_identical_step(arr1@, arr2@, arr3@, (index as int));

            if arr1@[old_index as int] == arr2@[old_index as int] && arr2@[old_index as int] == arr3@[old_index as int] {
                assert(count == old_count + 1);
                assert(
                    count_identical(
                        arr1@.subrange(0, (index as int)),
                        arr2@.subrange(0, (index as int)),
                        arr3@.subrange(0, (index as int)),
                    )
                        == count_identical(
                            arr1@.subrange(0, (old_index as int)),
                            arr2@.subrange(0, (old_index as int)),
                            arr3@.subrange(0, (old_index as int)),
                        ) + 1int
                );
                assert(
                    count_identical(
                        arr1@.subrange(0, (old_index as int)),
                        arr2@.subrange(0, (old_index as int)),
                        arr3@.subrange(0, (old_index as int)),
                    ) == old_count
                );
                assert(
                    count_identical(
                        arr1@.subrange(0, (index as int)),
                        arr2@.subrange(0, (index as int)),
                        arr3@.subrange(0, (index as int)),
                    ) == count
                );
            } else {
                assert(count == old_count);
                assert(
                    count_identical(
                        arr1@.subrange(0, (index as int)),
                        arr2@.subrange(0, (index as int)),
                        arr3@.subrange(0, (index as int)),
                    )
                        == count_identical(
                            arr1@.subrange(0, (old_index as int)),
                            arr2@.subrange(0, (old_index as int)),
                            arr3@.subrange(0, (old_index as int)),
                        ) + 0int
                );
                assert(
                    count_identical(
                        arr1@.subrange(0, (old_index as int)),
                        arr2@.subrange(0, (old_index as int)),
                        arr3@.subrange(0, (old_index as int)),
                    ) == old_count
                );
                assert(
                    count_identical(
                        arr1@.subrange(0, (index as int)),
                        arr2@.subrange(0, (index as int)),
                        arr3@.subrange(0, (index as int)),
                    ) == count
                );
            }
        }
    }

    proof {
        lemma_subrange_all(arr1@, (index as int));
        lemma_subrange_all(arr2@, (index as int));
        lemma_subrange_all(arr3@, (index as int));
    }

    count
}

}