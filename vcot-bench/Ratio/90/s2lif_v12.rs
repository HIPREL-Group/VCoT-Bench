use vstd::prelude::*;
fn main() {}
verus! {

// Complete the lemma function below
proof fn lemma_forall_extend_prefix_update_to_one(a_old: Seq<i32>, i: usize)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < (N as usize))
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof;

        let ghost prev_a_view = a@;

        a.set(i, 1);

        // Fill in a block of assertions here to complete the proof

        i = i + 1;

        // Fill in a block of assertions here to complete the proof;
    }

    i = 0;
    while (i < (N as usize))
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof;

        if (a[i] == 1) {
            let temp = a[i];
            a.set(i, temp + 2);
            assert(a@[(i as int)] == 3) by {
                assert(temp == 1);
            };
        } else {
            let temp = a[i];
            a.set(i, temp - 1);
        }

        // Fill in a block of assertions here to complete the proof

        i = i + 1;
    }

    i = 0;
    while (i < (N as usize))
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof;

        let temp = sum[0] + a[i];
        // Fill in a block of assertions here to complete the proof;
        sum.set(0, temp);
        // Fill in a block of assertions here to complete the proof;

        i = i + 1;
    }

    assert(sum[0] == 3 * N) by {
        assert(sum[0] == 3 * i);
        assert(i == (N as usize));
        assert(3 * (N as usize) == 3 * (N as int)) by {
            assert(((N as usize) as int) == (N as int));
        }
        assert(sum[0] == 3 * (N as int));
    };
}

}