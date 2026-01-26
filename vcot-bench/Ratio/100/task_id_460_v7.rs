use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_vec_len_after_push<T>(v: Seq<T>, x: T)
    

// Complete the lemma function below
proof fn lemma_vec_index_after_push_new<T>(v: Seq<T>, x: T)
    

spec fn w_index<T>(old_v: Seq<T>, x: T, k: int) -> T {
    old_v.push(x)[k]
}

// Complete the lemma function below
proof fn lemma_forall_push_extend_exact(
    old_first: Seq<i32>,
    pushed: Seq<i32>,
    arr: &Vec<Vec<i32>>,
    index_before: int,
    new_val: i32,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
    requires
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr@[i].len() > 0,
    ensures
        arr.len() == result.len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] result@[i] == #[trigger] arr@[i]@[0],
{
    let mut first_elem_arr: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        let seq = &arr[index];
        
        // Fill in a block of assertions here to complete the proof;
        
        let val = seq[0];

        let ghost old_first = first_elem_arr@;

        first_elem_arr.push(val);
        
        let ghost pushed = first_elem_arr@;

        // Fill in a block of assertions here to complete the proof

        index += 1;

        // Fill in a block of assertions here to complete the proof
    }
    first_elem_arr
}

}