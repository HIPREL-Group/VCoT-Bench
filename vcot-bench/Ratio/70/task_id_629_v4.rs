use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_take_succ_drop_last<T>(s: Seq<T>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        s.take(i + 1).drop_last() == s.take(i),
{
    assert(s.take(i + 1).len() == i + 1);
    assert(s.take(i + 1).drop_last().len() == i);
    assert(s.take(i).len() == i);

    assert forall |k: int|
        0 <= k < i
    implies
        s.take(i + 1).drop_last().index(k) == s.take(i).index(k)
    by {
        assert(k < s.take(i + 1).drop_last().len());
        assert(k < s.take(i + 1).len() - 1);

        assert(s.take(i + 1).index(k) == s.index(k));
        assert(s.take(i).index(k) == s.index(k));

        assert(s.take(i + 1).drop_last().index(k) == s.take(i + 1).index(k));
    };

    assert(s.take(i + 1).drop_last() == s.take(i));
}

// Complete the lemma function below
proof fn lemma_take_all<T>(s: Seq<T>)
    

#[verifier::exec_allows_no_decreases_clause]
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let input_len = arr.len();

    // Fill in a block of assertions here to complete the proof;

    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            even_numbers@ == arr@.take(index as int).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }

        // Fill in a block of assertions here to complete the proof
        index += 1;
    }

    // Fill in a block of assertions here to complete the proof;
    even_numbers
}

} // verus!