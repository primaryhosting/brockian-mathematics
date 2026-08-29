import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The relativization barrier

We formalize the Baker–Gill–Solovay theorem in a *relativized query model* of
computation:

* A **string** is a `List Bool`, a **language** (equivalently an oracle) is a
  Boolean-valued function on strings.
* An **oracle machine** is given by a *computable* transition function
  `step : α × Trans → Str ⊕ Bool`, which, given the input and the transcript of
  the queries asked so far together with the oracle's answers, either asks a new
  query (`Sum.inl z`) or halts with a verdict (`Sum.inr b`).
* The resource that is counted is the number of steps (each step is either one
  oracle query or the final answer), and a machine is *polynomially bounded*
  when it is run for `c * (n+1)^d` steps on inputs of length `n`.

`PClass A` is the class of languages decided by a polynomially bounded
deterministic oracle machine with oracle `A`; `NPClass A` is the class of
languages accepted with a polynomially long certificate by a polynomially
bounded verifier with oracle `A`.

The theorem `CS.baker_gill_solovay` states that there is an oracle `A` with
`PClass A = NPClass A` and an oracle `B` with `PClass B ≠ NPClass B`.

Two features of this model should be kept in mind. Machines are required to be
computable, so there are only countably many of them, which is what makes the
diagonalization for `B` possible; and the amount of computation performed
between two queries is unrestricted, only the number of steps is. Consequently
the collapsing oracle can be taken to be the empty oracle `emptyLang`: with no
useful oracle, both classes consist exactly of the decidable languages, since a
deterministic machine may scan all polynomially long certificates in a single
step. The separating oracle `B` is built by the usual stage construction: at
stage `i` one diagonalizes against the `i`-th machine at a length `N` where the
machine's step bound is smaller than the number `2 ^ N` of candidate strings.
-/

namespace CS

/-- Strings are finite bit sequences. -/
abbrev Str := List Bool

/-- A language, equivalently an oracle, is an indicator function on strings. -/
abbrev Lang := Str → Bool

/-- A transcript records the queries made so far together with their answers. -/
abbrev Trans := List (Str × Bool)

/-- An oracle machine with input type `α`: a computable function which, from the
input and the transcript so far, either issues a new oracle query or halts with
a verdict. -/
structure Machine (α : Type) [Primcodable α] : Type where
  /-- The transition function. -/
  step : α × Trans → Str ⊕ Bool
  /-- The transition function is computable. -/
  hstep : Computable step

section Model

variable {α : Type} [Primcodable α]

/-- A configuration: the input, the transcript so far, and the verdict (if the
machine has already halted). -/
abbrev Config (α : Type) := α × Trans × Option Bool

/-- One step of the machine with oracle `O`. -/

lemma poly_lt_two_pow (c d : ℕ) : ∃ N, ∀ n, N ≤ n → polyBound c d n < 2 ^ n := by
  have h := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d (r := 2) (by norm_num)
  have hpos : (0:ℝ) < (c : ℝ) * 2 ^ d + 1 := by positivity
  have h2 := h.def (c := (1 : ℝ) / ((c : ℝ) * 2 ^ d + 1)) (by positivity)
  rw [Filter.eventually_atTop] at h2
  obtain ⟨N, hN⟩ := h2
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hNn : N ≤ n := le_trans (le_max_left N 1) hn
  have key := hN n hNn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)] at key
  have hcast : ((polyBound c d n : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
    push_cast [polyBound]
    have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have h1 : ((n : ℝ) + 1) ^ d ≤ (2 * (n:ℝ)) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    have h2 : (2 * (n:ℝ)) ^ d = 2 ^ d * (n:ℝ) ^ d := by rw [mul_pow]
    have h3 : (c:ℝ) * ((n:ℝ) + 1) ^ d ≤ (c:ℝ) * 2 ^ d * (n:ℝ)^d := by
      have hc : (0:ℝ) ≤ (c:ℝ) := by positivity
      nlinarith [h1, h2]
    have h4 : (c:ℝ) * 2 ^ d * (n:ℝ)^d ≤ (c:ℝ) * 2 ^ d * ((1 / ((c : ℝ) * 2 ^ d + 1)) * 2 ^ n) := by
      have : (0:ℝ) ≤ (c:ℝ) * 2 ^ d := by positivity
      nlinarith [key]
    have h5 : (c:ℝ) * 2 ^ d * ((1 / ((c : ℝ) * 2 ^ d + 1)) * 2 ^ n) < 2 ^ n := by
      have h2n : (0:ℝ) < 2 ^ n := by positivity
      have hlt : (c:ℝ) * 2 ^ d * (1 / ((c : ℝ) * 2 ^ d + 1)) < 1 := by
        rw [mul_one_div, div_lt_one hpos]
        linarith
      nlinarith
    linarith
  exact_mod_cast hcast

open Classical in
/-- A threshold beyond which the polynomial bound `c * (n+1)^d` is smaller than
the number `2^n` of strings of length `n`. -/
