use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_i32_mod3_in_range(i: int)
    ensures
        (i % 3 == 0 || i % 3 == 1 || i % 3 == 2),
{
    let r = i % 3;
    assert(0 <= r) by {
        assert(0 < 3);
        assert(0 <= i % 3);
    }
    assert(r < 3) by {
        assert(0 < 3);
        assert(i % 3 < 3);
    }
    assert(r == 0 || r == 1 || r == 2) by {
        if r == 0 {
        } else if r == 1 {
        } else {
            assert(r == 2) by {
                assert(r != 0);
                assert(r != 1);
                assert(0 <= r && r < 3);
            }
        }
    }
}

// Complete the lemma function below
proof fn lemma_set_extends_prefix_range3(a: &Vec<i32>, i: usize)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        // Fill in loop invariants here
    {
        let tmp = (i % 3) as i32;

        // Fill in a block of assertions here to complete the proof

        a.set(i, tmp);

        // Fill in a block of assertions here to complete the proof

        i = i + 1;

        // Fill in a block of assertions here to complete the proof
    }

    i = 0;

    while (i < N as usize)
        // Fill in loop invariants here
    {
        if (i == 0) {
            sum.set(0, 0);

            // Fill in a block of assertions here to complete the proof
        } else {
            let ai = a[i];
            // Fill in a block of assertions here to complete the proof

            let sum_old = sum[0];
            assert(sum_old <= 2 * (i as i32)) by {
                assert(i > 0 ==> sum[0] <= 2 * i);
            }

            let temp = sum_old + a[i];
            sum.set(0, temp);

            // Fill in a block of assertions here to complete the proof
        }
        i = i + 1;
    }

    // Fill in a block of assertions here to complete the proof
}

}