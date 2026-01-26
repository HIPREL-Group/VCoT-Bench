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
        invariant 
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
    {  
        if (v[i] <= e) {
            // Capture the state of result before modification to trigger the loop invariant
            let ghost result_pre = result@;
            result.push(v[i]);
            proof {
                // Prove the new element is in result (fix for assertion failure)
                assert(result[(result.len() as int) - 1] == v[(i as int)]);
                assert(result@.contains(v[(i as int)]));

                // Prove preservation of the invariant for previous elements (fix for invariant failure)
                assert forall |k:int| 0 <= k < i && v[k] <= e implies result@.contains(v[k]) by {
                    // The loop invariant ensures result_pre contains v[k]
                    // This assertion triggers the invariant instantiation for k
                    assert(result_pre.contains(v[k]));
                    
                    // Show that containment in result_pre implies containment in result
                    let idx = choose|idx| 0 <= idx < result_pre.len() && result_pre[idx] == v[k];
                    // Since result extends result_pre, the element is at the same index
                    assert(result[idx] == v[k]);
                }
            }
        }

        i = i + 1;
    }  

    // Fill in a block of assertions here to complete the proof

    result
}
}