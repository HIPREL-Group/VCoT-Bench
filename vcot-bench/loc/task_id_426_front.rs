use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_filter_take_succ_u32(s: Seq<u32>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.take(i + 1).filter(|x: u32| x % 2 != 0)
        == if s.index(i) % 2 != 0 {
            s.take(i).filter(|x: u32| x % 2 != 0).push(s.index(i))
        } else {
            s.take(i).filter(|x: u32| x % 2 != 0)
        },
    decreases i,
{
    reveal(Seq::filter);
    let s_next = s.take(i + 1);
    assert(s_next.drop_last() =~= s.take(i));
    assert(s_next.last() == s[i]);
}

#[verifier::exec_allows_no_decreases_clause]
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;
    
    // Fill in a block of assertions here to complete the proof

    while index < arr.len()
        // Fill in loop invariants here
    {
        proof {
            lemma_filter_take_succ_u32(arr@, (index as int));
        }

        if (arr[index] % 2 != 0) {
            odd_list.push(arr[index]);

            proof {
                let prev_index_int: int = (index as int);
                let next_index_int: int = prev_index_int + 1;

                let prev_take = arr@.take(prev_index_int);
                let next_take = arr@.take(next_index_int);

                assert(arr[(index as int)] == arr@.index(prev_index_int));

                assert(
                    next_take.filter(|x: u32| x % 2 != 0)
                    == prev_take.filter(|x: u32| x % 2 != 0).push(arr[(index as int)])
                );

                assert(odd_list@ == prev_take.filter(|x: u32| x % 2 != 0).push(arr[(index as int)]));
                assert(odd_list@ == next_take.filter(|x: u32| x % 2 != 0));
            }
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