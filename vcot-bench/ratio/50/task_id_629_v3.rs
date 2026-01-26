use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_take_succ_drop_last<T>(s: Seq<T>, i: int)
   

proof fn lemma_take_all<T>(s: Seq<T>)
    ensures
        s.take(s.len() as int) == s,
{
    assert(s.take(s.len() as int).len() == s.len());
    assert forall |k:int| 0 <= k < s.len()
    implies s.take(s.len() as int).index(k) == s.index(k) by {
        assert(s.take(s.len() as int).index(k) == s.index(k));
    }
    assert(s.take(s.len() as int) == s);
}

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

        proof {
            lemma_take_succ_drop_last(arr@, (index as int));
            assert(arr@.take(((index + 1) as int)).drop_last() == arr@.take((index as int)));

            reveal(Seq::filter);
        }
        index += 1;
    }

    // Fill in a block of assertions here to complete the proof;
    even_numbers
}

} // verus!