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

theorem collapse : PClass emptyLang = NPClass emptyLang := by
  apply Set.eq_of_subset_of_subset
  · rintro L ⟨M, c, d, hM⟩
    refine ⟨padMachine M, c, d, fun x => ?_⟩
    constructor
    · intro hx
      exact ⟨[], Nat.zero_le _, by rw [run_padMachine, hM x, hx]⟩
    · rintro ⟨y, -, hy⟩
      rw [run_padMachine, hM x] at hy
      exact Option.some_injective _ hy
  · rintro L ⟨V, c, d, hV⟩
    refine ⟨constMachine (npDecide V emptyLang c d)
      (computable_npDecide V emptyLang computable_emptyLang c d), c + 1, d, fun x => ?_⟩
    have hk : 1 ≤ polyBound (c + 1) d x.length := by
      have hpos : 0 < (x.length + 1) ^ d := by positivity
      simp only [polyBound]
      nlinarith
    rw [run_constMachine _ _ emptyLang x hk]
    have hequiv := (npDecide_eq_true V emptyLang c d x).trans (hV x).symm
    cases hn : npDecide V emptyLang c d x <;> cases hL : L x <;>
      simp [hn, hL] at hequiv ⊢

/-! ## An oracle separating the classes -/

/-- The test language: `x ∈ LB B` iff the oracle `B` contains some string of
length `|x|`. (Membership only depends on the length of `x`.) -/
