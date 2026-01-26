use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::exec_allows_no_decreases_clause]
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2]
    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
{  
    let mut i: usize = 0;
    let vlen = v.len();
    let mut result: Vec<i32> = vec![];

    while (i < v.len()) 
        // Fill in loop invariants here
    {  
        if (v[i] <= e) {
            // Capture the state of result before modification to trigger the loop invariant
            let ghost result_pre = result@;
            result.push(v[i]);
            // Fill in a block of assertions here to complete the proof
        }

        i = i + 1;
    }  

    proof {
        assert(i == v.len());
        assert(vlen == v.len());
        assert(forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k])) by {
            assert forall |k:int| 0 <= k < v.len() && v[k] <= e implies result@.contains(v[k]) by {
                assert(0 <= k < (i as int));
            }
        }
    }

    result
}
}