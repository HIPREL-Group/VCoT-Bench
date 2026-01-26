use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_forall_extend_by_one(a: &Vec<u32>, i: usize)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
    requires
        old(a).len() == N,
        N <= 0x7FFF_FFFF,
    ensures
        sum <= 2*N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len()==N,
            forall|j:int| 0<=j<i ==> a[j]<=2,
    {
        assert(i < a.len());
        assert(i < N as usize);

        if (a[i] > 2) {
            a.set(i, 2);
            assert(a[(i as int)] == 2);
            // Fill in a block of assertions here to complete the proof;
        } else {
            // Fill in a block of assertions here to complete the proof;
        }

        // Fill in a block of assertions here to complete the proof;

        i = i + 1;
    }

    i = 0;
    let mut sum: u32 = 0;

    while (i < N as usize)
        invariant
            i<=N,
            N <= 0x7FFF_FFFF,
            a.len()==N,
            forall|j:int| 0<=j<N ==> a[j]<=2,
            sum<=2 * i,
    {
        assert(i < a.len());
        assert(i < N as usize);

        // Fill in a block of assertions here to complete the proof;

        assert(sum + a[(i as int)] <= 2 * (i as u32 + 1));

        sum = sum + a[i];
        i = i + 1;

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof

    sum
}

}