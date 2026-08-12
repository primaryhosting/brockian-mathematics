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
def DTIME (t : ℕ → ℕ) : Set (Set ℕ) :=
  {L | ∃ c : Nat.Partrec.Code, ∀ n, evaln (t n) c n = some (if n ∈ L then 1 else 0)}

/-- Giving a program more time can only increase the class of languages it decides. -/
theorem DTIME_mono {t t' : ℕ → ℕ} (h : ∀ n, t n ≤ t' n) : DTIME t ⊆ DTIME t' := by
  rintro L ⟨c, hc⟩
  exact ⟨c, fun n => evaln_mono (h n) (hc n)⟩

/-- The bit computed by the diagonal language at input `n`: it is `1` exactly when the
`n`-th program, run on input `n` with `t n` steps of fuel, fails to output `1`. -/
def diagBit (t : ℕ → ℕ) (n : ℕ) : ℕ :=
  if evaln (t n) (ofNat Nat.Partrec.Code n) n = some 1 then 0 else 1

/-- The diagonal language: those `n` such that the `n`-th program does not accept `n`
within `t n` steps. -/
def diagLang (t : ℕ → ℕ) : Set ℕ := {n | diagBit t n = 1}

theorem diagBit_eq_ite (t : ℕ → ℕ) (n : ℕ) :
    diagBit t n = if n ∈ diagLang t then 1 else 0 := by
  unfold diagLang diagBit
  by_cases h : evaln (t n) (ofNat Nat.Partrec.Code n) n = some 1 <;> simp [h]

theorem computable_diagBit {t : ℕ → ℕ} (ht : Computable t) : Computable (diagBit t) := by
  have he : Computable fun n => evaln (t n) (ofNat Nat.Partrec.Code n) n :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp
      (((ht.pair (Primrec.ofNat Nat.Partrec.Code).to_comp)).pair Computable.id)
  have hb : Computable fun n => decide (evaln (t n) (ofNat Nat.Partrec.Code n) n = some 1) :=
    Computable₂.comp (Primrec.eq (α := Option ℕ)).decide.to_comp he
      (Computable.const (some 1))
  exact (Computable.cond hb (Computable.const 0) (Computable.const 1)).of_eq fun n => by
    unfold diagBit; cases h : decide (evaln (t n) (ofNat Nat.Partrec.Code n) n = some 1) <;>
      simp_all

/-- The diagonal language is not decidable within time `t`. -/
theorem diagLang_not_mem_DTIME (t : ℕ → ℕ) : diagLang t ∉ DTIME t := by
  rintro ⟨c, hc⟩
  set n := Nat.Partrec.Code.encodeCode c with hn
  have hdec : ofNat Nat.Partrec.Code n = c := by
    rw [hn, ← Nat.Partrec.Code.encodeCode_eq]
    exact Denumerable.ofNat_encode c
  have h := hc n
  rw [← diagBit_eq_ite] at h
  unfold diagBit at h
  rw [hdec] at h
  by_cases hc1 : evaln (t n) c n = some 1
  · rw [if_pos hc1] at h
    rw [h] at hc1
    simp at hc1
  · rw [if_neg hc1] at h
    exact hc1 h

/-- **Time hierarchy theorem.**  For every computable time bound `t` there is a larger time
bound `t'` such that strictly more languages are decidable in time `t'` than in time `t`.
The separating language is the diagonal language `diagLang t`. -/
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

