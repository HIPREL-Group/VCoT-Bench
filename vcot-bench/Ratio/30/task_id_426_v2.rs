use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_filter_take_succ_u32(s: Seq<u32>, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;
    
    proof {
        reveal(Seq::filter);
        assert(odd_list@ == arr@.take(index as int).filter(|x: u32| x % 2 != 0));
    }

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            odd_list@ == arr@.take(index as int).filter(|x: u32| x % 2 != 0),
    {
        proof {
            lemma_filter_take_succ_u32(arr@, (index as int));
        }

        if (arr[index] % 2 != 0) {
            odd_list.push(arr[index]);

            // Fill in a block of assertions here to complete the proof
        } else {
            proof {
                let prev_index_int: int = (index as int);
                let next_index_int: int = prev_index_int + 1;

                let prev_take = arr@.take(prev_index_int);
                let next_take = arr@.take(next_index_int);

                assert(arr[(index as int)] == arr@.index(prev_index_int));

                assert(
                    next_take.filter(|x: u32| x % 2 != 0)
                    == prev_take.filter(|x: u32| x % 2 != 0)
                );

                assert(odd_list@ == prev_take.filter(|x: u32| x % 2 != 0));
                assert(odd_list@ == next_take.filter(|x: u32| x % 2 != 0));
            }
        }

        index += 1;
    }
    assert(arr@ == arr@.take(input_len as int));
    odd_list
}

}