#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
spec fn fibo(n: int) -> nat
    decreases n
{
    if n <= 0 { 0 } else if n == 1 { 1 }
    else { fibo(n - 2) + fibo(n - 1) }
}

spec fn fibo_fits_i32(n: int) -> bool {
    fibo(n) < 0x8000_0000
}

// Complete the lemma function below
proof fn fibo_is_monotonic(i: int, j: int)
   

// Complete the lemma function below
proof fn lemma_fibo_fits_i32_monotone_prefix(i: usize, n: usize)
   

#[verifier::exec_allows_no_decreases_clause]
fn fibonacci(n: usize) -> (ret: Vec<i32>)
requires
    fibo_fits_i32(n as int),
    n >= 2,
ensures
    forall |i: int| 2 <= i < n ==> #[trigger] ret@[i] ==  fibo(i),
    ret@.len() == n,
{
    let mut fib = Vec::new();
    fib.push(0);
    fib.push(1);
    let mut i = 2;

    while i < n
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof
        let next_fib = fib[i - 1] + fib[i - 2];

        fib.push(next_fib);

        i += 1;
    }

    fib
}
}