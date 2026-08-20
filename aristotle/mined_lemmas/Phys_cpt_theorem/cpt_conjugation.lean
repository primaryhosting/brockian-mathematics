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

theorem cpt_conjugation (T : WightmanTheory) {m : ℕ} (x : Fin (m + 1) → Spacetime)
    (hx : IsJostPoint x) :
    (T.W (m + 1) fun i => emb (-x i)) = (starRingEnd ℂ) (T.W (m + 1) fun i => emb (x i)) := by
  have h1 : (fun i : Fin (m + 1) => emb (-x i)) = fun i => -emb (x i) := by
    funext i; rw [emb_neg]
  rw [h1, inversion_invariance T (m + 1) fun i => emb (x i), T.hermiticity (m + 1) x]
  exact (T.weak_locality m x hx).symm

/-! ## Consistency: a nontrivial theory satisfying all the axioms -/

