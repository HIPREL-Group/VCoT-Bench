use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 2 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        // Fill in loop invariants here
    {
        a.set(i, 1);

        // Fill in a block of assertions here to complete the proof;

        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof;

        if (a[i] == 1) {
            let temp = a[i] + 1;
            a.set(i, temp);
            // Fill in a block of assertions here to complete the proof;
        } else {
            assert(false) by {
                assert(a[i as int] == 1);
            };
            let temp = a[i] - 1;
            a.set(i, temp);
        }

        // Fill in a block of assertions here to complete the proof;

        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof;

        let temp = sum[0] + a[i];
        // Fill in a block of assertions here to complete the proof;
        sum.set(0, temp);

        // Fill in a block of assertions here to complete the proof;

        i = i + 1;
    }

    assert(i == N as usize);

    assert(sum[0] == 2 * N) by {
        assert(sum[0] == 2 * i);
        assert(i == N as usize);
    };
}
}