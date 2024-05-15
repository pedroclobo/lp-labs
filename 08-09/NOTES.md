# Loops

1. The `always_loop_hoare` theorem states that is a program never terminates, we can prove anything we'd like about its postcondition. As `valid_hoare_triple` asserts that the postcondition must hold only when the program terminates, we are exercising a partial correctness logic.

2. The main difficulty in using the proof rule for loops is finding a suitable loop invariant. The loop invariant must be strong enough to prove the postcondition, but weak enough to be provable. The loop invariant is the `P`.

# Decorated Programs

1. The division example uses a loop. Therefore, it is needed to find a loop invariant for the loop.
