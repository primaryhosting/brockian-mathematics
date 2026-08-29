/-
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- **Rice's theorem.**  Let `C` be any set of partial functions `ℕ →. ℕ`, i.e. a *semantic*
property of programs (it depends only on the partial function a program computes).  If `C` is
nontrivial, in the sense that some program's semantics lies in `C` and some other program's
semantics does not, then the property "the program `c` has semantics in `C`" is undecidable. -/
theorem rice_nontrivial (C : Set (ℕ →. ℕ))
    (hin : ∃ a : Code, a.eval ∈ C) (hout : ∃ b : Code, b.eval ∉ C) :
    ¬ ComputablePred (fun c : Code => c.eval ∈ C) := by
  rintro hC
  obtain ⟨a, ha⟩ := hin
  obtain ⟨b, hb⟩ := hout
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.1 hC
  -- `g` flips the property: if `c` has the property, `g c` does not, and vice versa.
  set g : Code → Code := fun c => if f c then b else a with hg
  have hgc : Computable g := by
    simpa [hg, Bool.cond_eq_ite] using (Computable.cond hf (Computable.const b) (Computable.const a))
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.fixed_point hgc
  have hprop : (c.eval ∈ C) = (f c = true) := congrFun hfe c
  by_cases h : f c = true
  · have hcC : c.eval ∈ C := by rw [hprop]; exact h
    have : (g c).eval = b.eval := by simp [hg, h]
    exact hb (this ▸ hc ▸ hcC)
  · have hcC : c.eval ∉ C := by rw [hprop]; exact h
    have : (g c).eval = a.eval := by simp [hg, h]
    exact hcC (hc ▸ this ▸ ha)

/-- **Rice's theorem**, phrased for predicates on programs.  A predicate `P` on codes that is
*semantic* (it only depends on the partial function `c.eval` the code computes) and *nontrivial*
(it holds of some code and fails of some code) is not decidable. -/
theorem rice_nontrivial_pred (P : Code → Prop)
    (hsem : ∀ c d : Code, c.eval = d.eval → (P c ↔ P d))
    (hin : ∃ c : Code, P c) (hout : ∃ c : Code, ¬ P c) :
    ¬ ComputablePred P := by
  rintro hP
  obtain ⟨a, ha⟩ := hin
  obtain ⟨b, hb⟩ := hout
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.1 hP
  set g : Code → Code := fun c => if f c then b else a with hg
  have hgc : Computable g := by
    simpa [hg, Bool.cond_eq_ite] using
      (Computable.cond hf (Computable.const b) (Computable.const a))
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.fixed_point hgc
  have hprop : P c = (f c = true) := congrFun hfe c
  by_cases h : f c = true
  · have hcP : P c := by rw [hprop]; exact h
    have hgb : g c = b := by simp [hg, h]
    exact hb ((hsem b c (by rw [← hgb]; exact hc)).2 hcP)
  · have hcP : ¬ P c := by rw [hprop]; exact h
    have hga : g c = a := by simp [hg, h]
    exact hcP ((hsem a c (by rw [← hga]; exact hc)).1 ha)

/-- A concrete instance of Rice's theorem: it is undecidable whether a program halts on input `0`
with output `0`. -/
theorem outputs_zero_on_zero_undecidable :
    ¬ ComputablePred (fun c : Code => c.eval 0 = Part.some 0) := by
  refine rice_nontrivial_pred _ (fun c d h => by rw [h]) ⟨Code.zero, rfl⟩ ⟨Code.succ, ?_⟩
  have h1 : (Code.succ).eval 0 = Part.some 1 := by simp [Nat.Partrec.Code.eval]
  simp [h1]

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

