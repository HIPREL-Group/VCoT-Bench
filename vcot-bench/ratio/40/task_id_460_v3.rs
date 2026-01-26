use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_vec_len_after_push<T>(v: Seq<T>, x: T)
    ensures
        v.push(x).len() == v.len() + 1,
{
    let w = v.push(x);
    assert(w.len() == v.len() + 1);
}

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
        invariant
            0 <= index <= arr.len(),
            first_elem_arr.len() == index,
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr@[i].len() > 0,
            forall|k: int| 0 <= k < index ==> #[trigger] first_elem_arr@[k] == #[trigger] arr@[k]@[0],
    {
        let seq = &arr[index];
        
        assert(arr@[(index as int)].len() > 0);
        
        let val = seq[0];

        let ghost old_first = first_elem_arr@;

        first_elem_arr.push(val);
        
        let ghost pushed = first_elem_arr@;

        // Fill in a block of assertions here to complete the proof

        index += 1;

        proof {
            let idx_before: int = (index - 1) as int;
            lemma_forall_push_extend_exact(old_first, pushed, arr, idx_before, val);
        }
    }
    first_elem_arr
}

}