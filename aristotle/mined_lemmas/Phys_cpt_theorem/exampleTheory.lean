/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Real Minkowski space `ℝ^{1,3}`. -/
abbrev Spacetime := Fin 4 → ℝ

/-- Complexified Minkowski space `ℂ^4`, the domain of the analytically continued
Wightman functions. -/
abbrev CSpace := Fin 4 → ℂ

/-- The Minkowski bilinear form on real Minkowski space (signature `+ - - -`). -/

noncomputable def exampleTheory : WightmanTheory where
  W := fun _ z => ∑ i, ∑ j, cform (z i) (z j)
  bhw_covariance := by
    intro L _ _ hL n z
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hL 1 (z i) (z j)
  hermiticity := by
    intro n x
    have hreal : ∀ a b : Spacetime,
        (starRingEnd ℂ) (cform (emb a) (emb b)) = cform (emb a) (emb b) := by
      intro a b
      simp [cform, emb]
    rw [map_sum]
    simp only [map_sum, hreal]
    exact (sum_rev_rev (fun i j => cform (emb (x i)) (emb (x j)))).symm
  weak_locality := by
    intro m x _
    exact sum_rev_rev (fun i j => cform (emb (x i)) (emb (x j)))

