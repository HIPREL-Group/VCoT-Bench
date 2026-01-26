use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_take_drop_last_step_u32(arr: Seq<u32>, i: int)
   

proof fn lemma_filter_append_u32(s1: Seq<u32>, s2: Seq<u32>)
    ensures
        (s1 + s2).filter(|y: u32| y % 2 != 0) == 
        s1.filter(|y: u32| y % 2 != 0) + s2.filter(|y: u32| y % 2 != 0),
    decreases s1.len()
{
    reveal(Seq::filter);
    if s1.len() == 0 {
        assert(s1 + s2 =~= s2);
    } else {
        let tail = s1.subrange(1, s1.len() as int);
        lemma_filter_append_u32(tail, s2);
        
        assert((seq![s1[0]] + tail) + s2 =~= seq![s1[0]] + (tail + s2));
        assert(s1 + s2 =~= seq![s1[0]] + (tail + s2));
    }
}

// Complete the lemma function below
proof fn lemma_filter_push_u32(s: Seq<u32>, x: u32)
    

#[verifier::exec_allows_no_decreases_clause]
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_numbers: Vec<u32> = Vec::new();
    let input_len = arr.len();

    proof {
        reveal(Seq::filter);
        assert(arr@.take(0).filter(|x: u32| x % 2 != 0) == Seq::<u32>::empty());
    }

    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            odd_numbers@ == arr@.take((index as int)).filter(|x: u32| x % 2 != 0),
    {
        if (arr[index] % 2 != 0) {
            odd_numbers.push(arr[index]);

            // Fill in a block of assertions here to complete the proof
        } else {
            proof {
                let i: int = index as int;
                assert(arr@.take(i + 1) =~= arr@.take(i).push(arr[i]));
                
                lemma_filter_push_u32(arr@.take(i), arr[i]);
                
                assert(arr@.take(i + 1).filter(|y: u32| y % 2 != 0)
                    == arr@.take(i).filter(|y: u32| y % 2 != 0));
            }
        }

        index += 1;
    }
    assert(arr@ == arr@.take((input_len as int)));
    odd_numbers
}

}