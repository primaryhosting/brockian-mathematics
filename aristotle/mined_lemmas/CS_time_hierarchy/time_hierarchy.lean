/-
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Statement: The time hierarchy theorem: more time gives strictly more languages (diagonalization).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Statement: The time hierarchy theorem: more time gives strictly more languages (diagonalization).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization notes

The model of computation is Mathlib's partial recursive `Nat.Partrec.Code`, whose
step-indexed evaluator `Nat.Partrec.Code.evaln k c n` runs the program `c` on input `n`
for `k` steps of fuel.  "Running time" is the amount of fuel consumed, and
`CS.DTIME t` is the class of languages decided within fuel `t n` on input `n`.

The theorem `CS.time_hierarchy` says: for every computable time bound `t` there is a
pointwise larger bound `t'` with `DTIME t ⊊ DTIME t'`, i.e. more time really does decide
strictly more languages.  The witness separating the two classes is the diagonal language
`CS.diagLang t = {n | the n-th program does not output 1 on input n within t n steps}`,
which is not in `DTIME t` by diagonalization, but is computable (because `evaln` is), hence
lies in `DTIME t'` for `t'` its own running time.
-/

open scoped Classical

open Nat.Partrec Nat.Partrec.Code Denumerable

namespace CS

/-- `DTIME t` is the class of languages `L ⊆ ℕ` decided within time bound `t`:
there is a program (a `Nat.Partrec.Code`) which, run on input `n` with `t n` steps of
fuel, halts and outputs `1` if `n ∈ L` and `0` otherwise.  Here "time" is measured by
the step-index (fuel) of Mathlib's step-indexed evaluator `Nat.Partrec.Code.evaln`. -/

theorem time_hierarchy (t : ℕ → ℕ) (ht : Computable t) :
    ∃ t' : ℕ → ℕ, (∀ n, t n ≤ t' n) ∧ DTIME t ⊂ DTIME t' := by
  obtain ⟨c, hcode⟩ :=
    Nat.Partrec.Code.exists_code.1
      (Partrec.nat_iff.1 (computable_diagBit ht).partrec)
  have hex : ∀ n, ∃ k, evaln k c n = some (diagBit t n) := by
    intro n
    have : diagBit t n ∈ eval c n := by rw [hcode]; simp
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 this
    exact ⟨k, hk⟩
  have hmem : diagLang t ∈ DTIME fun n => max (t n) (Nat.find (hex n)) := by
    refine ⟨c, fun n => ?_⟩
    rw [← diagBit_eq_ite]
    exact evaln_mono (le_max_right _ _) (Nat.find_spec (hex n))
  exact ⟨fun n => max (t n) (Nat.find (hex n)), fun n => le_max_left _ _,
    DTIME_mono fun n => le_max_left _ _,
    fun hsub => diagLang_not_mem_DTIME t (hsub hmem)⟩

end CS

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

