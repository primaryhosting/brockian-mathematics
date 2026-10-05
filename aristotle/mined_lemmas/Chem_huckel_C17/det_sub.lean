import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to come before any other command
(including module doc comments), so the header comment above is placed immediately after
the single `import Mathlib` line; its text is otherwise verbatim.

Mathematical content: the adjacency matrix `C17` of the cycle graph on 17 vertices is the
circulant matrix `A i j = 1` iff `i - j = ±1` (indices in `ZMod 17`).  It is diagonalised by
the discrete Fourier matrix `F i k = ζ^{ik}` (`ζ = exp (2πi/17)`), with eigenvalues
`ζ^k + ζ^{-k} = 2 cos (2πk/17)`.  Hence `det (μ - A) = ∏ (μ - 2 cos (2πk/17))`, and the
spectrum is exactly the set of these 17 numbers.
-/

namespace Chem

open Complex Matrix

/-- A primitive 17-th root of unity. -/

lemma det_sub (μ : ℂ) :
    (algebraMap ℂ (Matrix (ZMod 17) (ZMod 17) ℂ) μ - C17).det = ∏ k : ZMod 17, (μ - lam k) := by
  have key : algebraMap ℂ (Matrix (ZMod 17) (ZMod 17) ℂ) μ - C17
      = F * Matrix.diagonal (fun k => μ - lam k) * G := by
    have h1 : (Matrix.diagonal fun k : ZMod 17 => μ - lam k)
        = algebraMap ℂ (Matrix (ZMod 17) (ZMod 17) ℂ) μ - Matrix.diagonal lam := by
      rw [Matrix.algebraMap_eq_diagonal, ← Matrix.diagonal_sub]
      rfl
    have hc : F * algebraMap ℂ (Matrix (ZMod 17) (ZMod 17) ℂ) μ
        = algebraMap ℂ (Matrix (ZMod 17) (ZMod 17) ℂ) μ * F := (Algebra.commutes μ F).symm
    rw [h1, Matrix.mul_sub, hc, ← C17_mul_F, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      F_mul_G, Matrix.mul_one, Matrix.mul_one]
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  rw [show F.det * (∏ k : ZMod 17, (μ - lam k)) * G.det
      = (F.det * G.det) * ∏ k : ZMod 17, (μ - lam k) by ring, det_F_mul_det_G, one_mul]

/-- **Hückel theory for the cycle `C₁₇`**: the spectrum of the adjacency matrix of the
cycle graph on 17 vertices is exactly `{2 cos (2πk/17) : k = 0, …, 16}`. -/
