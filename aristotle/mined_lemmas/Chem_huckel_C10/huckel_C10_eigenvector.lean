import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

theorem huckel_C10_eigenvector (k : ZMod 10) :
    C10adj *ᵥ (fun j => chi (j * k)) = C10eigen k • (fun j => chi (j * k)) := by
  funext i
  rw [adj_mulVec]
  have e1 : (i - 1) * k = i * k + -k := by ring
  have e2 : (i + 1) * k = i * k + k := by ring
  simp only [e1, e2, chi_add, Pi.smul_apply, smul_eq_mul]
  rw [← chi_add_neg]
  ring

/-- **Hückel theory for the C₁₀ cycle.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₀` if and only if `μ = 2 cos (2πk/10)` for some
`k ∈ {0,…,9}`. -/
