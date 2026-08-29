/-
/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean 4 requires `import` commands to precede any module docstring, so the required
-- header above is reproduced verbatim inside a comment block at the top of the file.)

import Mathlib

open scoped InnerProductSpace

namespace QPhys

/-- Applying a continuous `ℂ`-linear operator to a vector is a bounded `ℝ`-bilinear map.
(The Mathlib lemma `isBoundedBilinearMap_apply` only covers the case where the scalar field
of the operators coincides with the differentiability field; here we differentiate in `ℝ`
while the operators are `ℂ`-linear.) -/

theorem isBoundedBilinearMap_apply_real {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] :
    IsBoundedBilinearMap ℝ (fun p : (E →L[ℂ] E) × E => p.1 p.2) where
  add_left := by intros; simp
  smul_left := by intros; simp
  add_right := by intros; simp
  smul_right := by intros; simp
  bound := ⟨1, one_pos, by intro x y; simpa using x.le_opNorm y⟩

/-- Product rule for `s ↦ A s (u s)` where `A` is a curve of continuous `ℂ`-linear operators
and `u` a curve of vectors, both differentiated with respect to a real parameter. -/
