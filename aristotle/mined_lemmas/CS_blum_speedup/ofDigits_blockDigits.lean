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

theorem ofDigits_blockDigits (b : Nat) :
    ∀ (k d : Nat), d < b ^ k → ofDigits b (blockDigits b k d) = d := by
  intro k
  induction k with
  | zero =>
      intro d hd
      have : b ^ 0 = 1 := rfl
      have : d = 0 := by omega
      simp [blockDigits, ofDigits_nil, this]
  | succ k ih =>
      intro d hd
      have hb : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h | h
        · subst h
          rw [Nat.zero_pow (by omega)] at hd
          omega
        · exact h
      have hdb : d / b < b ^ k := by
        rw [Nat.div_lt_iff_lt_mul hb]
        rw [Nat.pow_succ] at hd
        omega
      show ofDigits b ((d % b) :: blockDigits b k (d / b)) = d
      rw [ofDigits_cons, ih _ hdb]
      exact Nat.mod_add_div d b

/-- The compressed machine: it works in base `base ^ k`, each of its steps consuming
one base-`base ^ k` digit, i.e. simulating `k` steps of `M`. -/
