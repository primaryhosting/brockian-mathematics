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

lemma lam_eq_cos (k : Fin 13) :
    lam k = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 13) := by
  have hz : ev k = Complex.exp ((((2 * Real.pi * (k : ℕ) / 13 : ℝ)) : ℂ) * Complex.I) := by
    rw [ev, zt, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz' : (ev k)⁻¹ = Complex.exp (-((((2 * Real.pi * (k : ℕ) / 13 : ℝ)) : ℂ) * Complex.I)) := by
    rw [hz, ← Complex.exp_neg]
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 13 with ht
  rw [lam, hz, hz']
  have h1 : Complex.exp ((t : ℂ) * Complex.I) = Complex.cos t + Complex.sin t * Complex.I :=
    Complex.exp_mul_I
  have h2 : Complex.exp (-((t : ℂ) * Complex.I)) = Complex.cos (-t) + Complex.sin (-t) * Complex.I := by
    have := Complex.exp_mul_I (z := -(t : ℂ))
    rw [← this]; ring_nf
  rw [h1, h2, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]
  ring

/-- The Vandermonde-type matrix of characters; its columns are the eigenvectors. -/
