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
