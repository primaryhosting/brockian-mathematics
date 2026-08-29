/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Matrix
open Complex

namespace Chem

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₀`. -/

lemma zk_add_inv (k : Fin 10) : zk k + (zk k)⁻¹ = mu k := by
  have h1 : zk k = Complex.exp (((2 * Real.pi * (k : ℕ) / 10 : ℝ) : ℂ) * Complex.I) := by
    rw [zk, zeta10, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h1, ← Complex.exp_neg, mu, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

