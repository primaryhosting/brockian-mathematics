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
