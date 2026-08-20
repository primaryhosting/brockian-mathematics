import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The real quadratic form `x ↦ ⟪x, M x⟫` associated to a matrix `M`
(taking the real part, which for Hermitian `M` loses no information). -/

lemma eigenvalues_one (h1 : (1 : Matrix (Fin d) (Fin d) ℂ).IsHermitian) (i : Fin d) :
    h1.eigenvalues i = 1 := by
  have hmem := h1.eigenvalues_mem_spectrum_real i
  by_contra hne
  rw [spectrum.mem_iff] at hmem
  apply hmem
  have hx : (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ)) (h1.eigenvalues i) - 1
      = ((h1.eigenvalues i : ℂ) - 1) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    simp [Algebra.algebraMap_eq_smul_one, sub_smul, Complex.coe_smul]
  rw [hx, Matrix.isUnit_iff_isUnit_det]
  simp
  intro h
  have : (h1.eigenvalues i : ℝ) - 1 = 0 := by exact_mod_cast h
  exact absurd (by linarith : h1.eigenvalues i = 1) hne

/-- Sanity check: the identity matrix has `d` strictly positive eigenvalues, so the
counting functions above are not degenerate. -/
