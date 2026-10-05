/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We prove: **there exist problems with no fastest algorithm** — a Blum-style speedup
phenomenon — in a completely explicit machine model with an explicit runtime measure.

*Machines.* A `DigitMachine` fixes a base `b ≥ 2` and is a finite-state streaming
machine: it reads the base-`b` digits of its input one digit per step (least
significant digit first), updating a state taken from a finite state set, and finally
outputs a bit determined by the state it ends in.

*Runtime.* The runtime (`cost`) of a machine on input `x` is the number of steps it
performs, i.e. the number of base-`b` digits of `x`.

*Speedup.* Recoding the input in base `b ^ k` lets one machine step consume `k` old
digits, dividing the runtime by `k`. Consequently, for the (nontrivial) problem
"is `x` divisible by `3`?", every algorithm is beaten, on all but finitely many
inputs, by another algorithm for the same problem, and by an arbitrarily large factor;
hence no fastest algorithm exists.

*Scope.* The statement proved here is "there exist problems with no fastest algorithm",
with the speedup obtained by input recoding in an explicit machine model with an
explicit runtime measure (`no_fastest_algorithm`, `blum_speedup`). The speedup factor
is linear (any factor `k`), so this is the recoding/linear-speedup form of the
phenomenon rather than Blum's recursion-theoretic construction with an arbitrary
total computable speedup function.

As in the classical argument, the price of the speedup is a larger transition table
(the compressed machine reads digits from a larger alphabet), not a slower step: each
step of any machine remains a single lookup in a finite control, and is charged one
unit of time.

The file is self-contained: it uses nothing beyond the Lean prelude.
-/

set_option autoImplicit false

namespace CS

/-! ## Numbers and digit strings -/

/-- The natural number represented by the digit list `L` in base `b`, least
significant digit first. -/

theorem DigitMachine.compress_cost_lt (M : DigitMachine) (x : Nat) (hx : M.base ≤ x) :
    (M.compress 2 (by omega)).cost x < M.cost x := by
  have h2 := numDigits_pow M.base M.two_le_base 2 (by omega) x
  have hb2 : 2 ≤ numDigits M.base x := by
    rcases Nat.lt_or_ge (numDigits M.base x) 2 with h | h
    · have h1 : numDigits M.base x ≤ 1 := by omega
      have h3 := (numDigits_le_iff M.base M.two_le_base 1 x).1 h1
      rw [Nat.pow_one] at h3
      omega
    · exact h
  show numDigits (M.base ^ 2) x < numDigits M.base x
  omega

/-! ## A concrete problem: divisibility by three -/

/-- The decision problem: "is `x` divisible by `3`?" -/
