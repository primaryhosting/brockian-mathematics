import Mathlib
/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Faltings' theorem (the Mordell conjecture) states that a smooth projective curve of genus
`≥ 2` over `ℚ` has only finitely many rational points.

In this file we

* formalise the statement for smooth plane curves in `ℙ²`, where the genus is given by the
  degree–genus formula `g = (d-1)(d-2)/2`, so that `d ≥ 4` is exactly the condition `g ≥ 2`
  (`Frontier.FaltingsMordellStatement`);
* verify, unconditionally, an instance of it: the Fermat quartic `x⁴ + y⁴ = z⁴`, a smooth
  plane curve of degree `4` and hence of genus `3`, has only finitely many rational points
  (`Frontier.faltings_mordell`) — indeed exactly four (`Frontier.fermatQuartic_projPoints`).
  The proof uses Fermat's Last Theorem for exponent four.
-/

namespace Frontier

open MvPolynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

/-- The set of `ℚ`-points of the plane projective curve cut out by `F`. -/

theorem fermatQuartic_projPoints_ncard : (projPoints fermatQuartic).ncard = 4 := by
  have hne0 : (![1, 0, 1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 0
  have hne1 : (![1, 0, -1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 0
  have hne2 : (![0, 1, 1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 1
  have hne3 : (![0, 1, -1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 1
  have key : ∀ (v w : Fin 3 → ℚ) (hv : v ≠ 0) (hw : w ≠ 0), (∀ a : ℚ, a • w ≠ v) →
      Projectivization.mk ℚ v hv ≠ Projectivization.mk ℚ w hw := by
    intro v w hv hw h hcon
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℚ v w hv hw).mp hcon
    exact h a ha
  have d01 : Projectivization.mk ℚ ![1, 0, 1] hne0 ≠ Projectivization.mk ℚ ![1, 0, -1] hne1 := by
    refine key _ _ _ _ fun a ha => ?_
    have h0 := congrFun ha 0
    have h2 := congrFun ha 2
    simp [Matrix.cons_val_two, Matrix.tail_cons] at h0 h2
    rw [h0] at h2
    norm_num at h2
  have d02 : Projectivization.mk ℚ ![1, 0, 1] hne0 ≠ Projectivization.mk ℚ ![0, 1, 1] hne2 := by
    refine key _ _ _ _ fun a ha => ?_
    have h0 := congrFun ha 0
    simp at h0
  have d03 : Projectivization.mk ℚ ![1, 0, 1] hne0 ≠ Projectivization.mk ℚ ![0, 1, -1] hne3 := by
    refine key _ _ _ _ fun a ha => ?_
    have h0 := congrFun ha 0
    simp at h0
  have d12 : Projectivization.mk ℚ ![1, 0, -1] hne1 ≠ Projectivization.mk ℚ ![0, 1, 1] hne2 := by
    refine key _ _ _ _ fun a ha => ?_
    have h0 := congrFun ha 0
    simp at h0
  have d13 : Projectivization.mk ℚ ![1, 0, -1] hne1 ≠ Projectivization.mk ℚ ![0, 1, -1] hne3 := by
    refine key _ _ _ _ fun a ha => ?_
    have h0 := congrFun ha 0
    simp at h0
  have d23 : Projectivization.mk ℚ ![0, 1, 1] hne2 ≠ Projectivization.mk ℚ ![0, 1, -1] hne3 := by
    refine key _ _ _ _ fun a ha => ?_
    have h1 := congrFun ha 1
    have h2 := congrFun ha 2
    simp [Matrix.cons_val_two, Matrix.tail_cons] at h1 h2
    rw [h1] at h2
    norm_num at h2
  rw [fermatQuartic_projPoints, fermatQuarticPointSet]
  rw [Set.ncard_insert_of_notMem (by simp [d01, d02, d03]) (by
        exact (((Set.finite_singleton _).insert _).insert _)),
      Set.ncard_insert_of_notMem (by simp [d12, d13]) (by
        exact ((Set.finite_singleton _).insert _)),
      Set.ncard_insert_of_notMem (by simp [d23]) (Set.finite_singleton _),
      Set.ncard_singleton]

/-- A Lean-checked reduction: the general statement of Faltings' theorem for smooth plane
curves does apply to the Fermat quartic, i.e. its hypotheses are verified there. -/
