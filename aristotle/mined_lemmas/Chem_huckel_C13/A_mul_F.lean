import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
(The `import Mathlib` line must precede the module docstring: Lean 4 requires all
`import` commands to appear at the very beginning of a file.)
-/

namespace Chem

open Matrix SimpleGraph Finset

/-- A primitive 13-th root of unity. -/

lemma A_mul_F : A * F = F * Matrix.diagonal lam := by
  ext i k
  have hne : ∀ i : Fin 13, i - 1 ≠ i + 1 := by decide
  have hsum : (A * F) i k = F (i - 1) k + F (i + 1) k := by
    have h1 : (A * F) i k = (A *ᵥ fun j => F j k) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, A, adjMatrix_mulVec_apply, cycleGraph_neighborFinset,
      Finset.sum_pair (hne i)]
  rw [hsum, Matrix.mul_diagonal, F_apply, F_apply, F_apply, lam]
  have e1 : ev ((i + 1) * k) = ev (i * k) * ev k := by
    rw [← ev_add]; ring_nf
  have e2 : ev ((i - 1) * k) * ev k = ev (i * k) := by
    rw [← ev_add]; ring_nf
  have e3 : ev ((i - 1) * k) = ev (i * k) * (ev k)⁻¹ := by
    field_simp [ev_ne_zero k] at e2 ⊢
    linear_combination e2
  rw [e1, e3]
  ring

