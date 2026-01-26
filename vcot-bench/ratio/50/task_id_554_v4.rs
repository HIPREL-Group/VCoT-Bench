use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_take_drop_last_step_u32(arr: Seq<u32>, i: int)
   

// Complete the lemma function below
proof fn lemma_filter_append_u32(s1: Seq<u32>, s2: Seq<u32>)
    

proof fn lemma_filter_push_u32(s: Seq<u32>, x: u32)
    ensures
        s.push(x).filter(|y: u32| y % 2 != 0)
        == if x % 2 != 0 { s.filter(|y: u32| y % 2 != 0).push(x) } else { s.filter(|y: u32| y % 2 != 0) },
{
    reveal_with_fuel(Seq::filter, 2);

    assert(s.push(x) =~= s + seq![x]);
    lemma_filter_append_u32(s, seq![x]);
    assert((s + seq![x]).filter(|y: u32| y % 2 != 0) == 
           s.filter(|y: u32| y % 2 != 0) + seq![x].filter(|y: u32| y % 2 != 0));
    
    if x % 2 != 0 {
        assert(seq![x].filter(|y: u32| y % 2 != 0) =~= seq![x]);
        assert(s.filter(|y: u32| y % 2 != 0) + seq![x] =~= s.filter(|y: u32| y % 2 != 0).push(x));
    } else {
        assert(x % 2 == 0);
        
        let singleton = seq![x];
        
        assert(singleton[0] == x);
        assert(singleton[0] % 2 == 0);

        let tail = singleton.subrange(1, singleton.len() as int);
        assert(tail =~= Seq::<u32>::empty());
        assert(singleton.filter(|y: u32| y % 2 != 0) =~= tail.filter(|y: u32| y % 2 != 0));
        assert(tail.filter(|y: u32| y % 2 != 0) =~= Seq::<u32>::empty());
        assert(s.filter(|y: u32| y % 2 != 0) + Seq::<u32>::empty() =~= s.filter(|y: u32| y % 2 != 0));
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_numbers: Vec<u32> = Vec::new();
    let input_len = arr.len();

    // Fill in a block of assertions here to complete the proof

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