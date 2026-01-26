use vstd::prelude::*;
fn main() {
}

verus! {

spec fn min_spec(seq: Seq<i32>) -> int
    recommends
        0 < seq.len(),
    decreases seq.len(),
{
    if seq.len() == 1 {
        seq[0] as int
    } else if seq.len() == 0 {
        0
    } else {
        let later_min = min_spec(seq.drop_first());
        if seq[0] <= later_min {
            seq[0] as int
        } else {
            later_min as int
        }
    }
}

proof fn lemma_min_spec_is_minimum(seq: Seq<i32>, i: int)
    requires
        0 < seq.len(),
        0 <= i < seq.len(),
    ensures
        seq[i] as int >= min_spec(seq),
    decreases seq.len(),
{
    if seq.len() == 1 {
        assert(i == 0);
        assert(min_spec(seq) == seq[0] as int);
    } else {
        let later = seq.drop_first();
        assert(later.len() == seq.len() - 1);
        assert(0 < later.len());

        if i > 0 {
            lemma_min_spec_is_minimum(later, i - 1);
        }

        let later_min = min_spec(later);
        if seq[0] <= later_min {
            assert(min_spec(seq) == seq[0] as int);
            if i == 0 {
            } else {
                assert(later[i - 1] == seq[i]);
                assert(seq[i] as int >= later_min);
                assert(later_min >= seq[0] as int);
            }
        } else {
            assert(min_spec(seq) == later_min as int);
            if i == 0 {
                assert(seq[0] as int > later_min);
            } else {
                assert(later[i - 1] == seq[i]);
                assert(seq[i] as int >= later_min);
            }
        }
    }
}

// Complete the lemma function below
proof fn lemma_min_index_gives_minimum(numbers: &Vec<i32>, m: usize)
   

// Complete the lemma function below
proof fn lemma_forall_extend_index<T>(
    P: spec_fn(int) -> bool,
    old_index: int,
    new_index: int,
)
   

proof fn lemma_forall_except_extend_index(
    numbers: &Vec<i32>,
    min_index: usize,
    second_min_index: usize,
    old_index: usize,
    new_index: usize,
)
    requires
        old_index <= new_index,
        0 <= min_index < old_index,
        0 <= second_min_index < old_index,
        min_index != second_min_index,
        forall|k: int|
            0 <= k < old_index && k != min_index ==> numbers[k] >= numbers[second_min_index as int],
    ensures
        forall|k: int|
            0 <= k < new_index && k != min_index ==> (k < old_index ==> numbers[k] >= numbers[second_min_index as int]),
{
    assert forall|k: int|
        0 <= k < new_index && k != min_index && k < old_index implies numbers[k] >= numbers[second_min_index as int] by {
        assert(numbers[k] >= numbers[second_min_index as int]);
    }
}

// Complete the lemma function below
proof fn lemma_vec_len_ge_2_implies_ge_1(numbers: &Vec<i32>)
   

// Complete the lemma function below
proof fn lemma_second_min_index_in_bounds(numbers: &Vec<i32>, min_index: usize, second_min_index: usize)
   

#[verifier::exec_allows_no_decreases_clause]
fn second_smallest(numbers: &Vec<i32>) -> (indices: (usize, usize))
    requires
        numbers.len() >= 2,
    ensures
        forall|k: int|
            0 <= k < numbers.len() && k != indices.0 && numbers[indices.0 as int] == min_spec(
                numbers@,
            ) ==> (#[trigger] numbers[k] >= numbers[indices.1 as int]),
        exists|k: int|
            0 <= k < numbers.len() && k != indices.0 && (#[trigger] numbers[k]
                == numbers[indices.1 as int]),
{
    let mut min_index: usize = 0;
    let mut second_min_index: usize = 1;

    if numbers[1] < numbers[0] {
        min_index = 1;
        second_min_index = 0;
    }
    let mut index = 2;
    while index < numbers.len()
        invariant
            0 <= index <= numbers.len(),
            0 <= min_index < index,
            0 <= second_min_index < index,
            min_index != second_min_index,
            forall|k: int| 0 <= k < index ==> numbers[k] >= numbers[min_index as int],
            forall|k: int|
                0 <= k < index && k != (min_index as int) ==> numbers[k] >= numbers[second_min_index as int],
    {
        if numbers[index] < numbers[min_index] {
            second_min_index = min_index;
            min_index = index;
        } else if numbers[index] < numbers[second_min_index] {
            second_min_index = index;
        }
        index += 1;

        assert(forall|k: int|
            0 <= k < index && k != (min_index as int) ==> numbers[k] >= numbers[second_min_index as int]) by {
            assert forall|k: int|
                0 <= k < index && k != (min_index as int) implies numbers[k] >= numbers[second_min_index as int] by {
                if k < index - 1 {
                    assert(numbers[k] >= numbers[second_min_index as int]);
                } else {
                    assert(numbers[k] == numbers[(index - 1) as int]);
                    assert(numbers[k] >= numbers[second_min_index as int]);
                }
            }
        };
    }
    // Fill in a block of assertions here to complete the proof;

    (min_index, second_min_index)
}

}