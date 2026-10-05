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

theorem numDigits_le_iff (b : Nat) (hb : 2 ≤ b) :
    ∀ (n x : Nat), numDigits b x ≤ n ↔ x < b ^ n := by
  intro n
  induction n with
  | zero =>
      intro x
      have hpow : b ^ 0 = 1 := rfl
      constructor
      · intro h
        rcases Nat.eq_zero_or_pos x with hx | hx
        · omega
        · rw [numDigits_succ b x hb hx] at h
          omega
      · intro h
        have hx : x = 0 := by omega
        rw [hx, numDigits_zero]
        omega
  | succ n ih =>
      intro x
      rcases Nat.eq_zero_or_pos x with hx | hx
      · subst hx
        constructor
        · intro _
          exact Nat.pow_pos (by omega)
        · intro _
          rw [numDigits_zero]
          omega
      · rw [numDigits_succ b x hb hx]
        have h1 : (1 + numDigits b (x / b) ≤ n + 1) ↔ (numDigits b (x / b) ≤ n) := by omega
        rw [h1, ih (x / b), Nat.pow_succ]
        exact Nat.div_lt_iff_lt_mul (by omega)

/-! ## The machine model -/

/-- A finite-state machine reading the base-`base` digits of its input, least
significant digit first, one digit per step, and returning a Boolean determined by the
state it ends in. -/
structure DigitMachine : Type 1 where
  /-- The base in which the input is presented. -/
  base : Nat
  /-- Inputs are presented in a base of at least two. -/
  two_le_base : 2 ≤ base
  /-- The set of internal states. -/
  State : Type
  /-- An explicit list of all states: the control is finite. -/
  states : List State
  /-- Every state occurs in `states`. -/
  states_complete : ∀ s : State, s ∈ states
  /-- The initial state. -/
  start : State
  /-- One computation step: read one digit and update the state. -/
  step : State → Nat → State
  /-- The output bit read off the final state. -/
  out : State → Bool

namespace DigitMachine

/-- The state reached after streaming the digit list `L` (least significant first). -/
