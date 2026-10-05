/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean 4 does not allow a module
-- docstring to precede the `import` commands; the same header is repeated below verbatim.)

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Hückel (tight-binding) Hamiltonian of the cyclic polyene `C₁₈` is, up to the affine
normalisation `H = α + β A`, the adjacency matrix `A` of the cycle graph `C₁₈`.
We prove that a complex number `μ` is an eigenvalue of that adjacency matrix precisely when
`μ = 2 cos (2πk/18)` for some `k ∈ {0, …, 17}`.

The vertex type of `SimpleGraph.cycleGraph 18` is `Fin 18`, which is `ZMod 18`; all index
arithmetic below is therefore modulo `18`.
-/

namespace Chem

open Complex Matrix Finset

/-- A primitive 18-th root of unity. -/

lemma eig_eq (k : ZMod 18) : eig k = 2 * Real.cos (2 * Real.pi * k.val / 18) := by
  have hchi : chi k = Complex.exp ((2 * Real.pi * k.val / 18 : ℝ) * Complex.I) := by
    rw [chi_apply, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hprod : chi k * chi (-k) = 1 := by rw [← chi_add, add_neg_cancel, chi_zero]
  have hne : chi k ≠ 0 := by rw [hchi]; exact Complex.exp_ne_zero _
  have hchi' : chi (-k) = Complex.exp (-(2 * Real.pi * k.val / 18 : ℝ) * Complex.I) := by
    have hinv : chi (-k) = (chi k)⁻¹ := by
      field_simp
      linear_combination hprod
    rw [hinv, hchi, ← Complex.exp_neg]
    congr 1
    ring
  rw [eig, hchi, hchi', Complex.ofReal_cos, Complex.cos]
  push_cast
  ring

/-- **Hückel spectrum of C₁₈.** A complex number `μ` is an eigenvalue of the adjacency matrix
of the cycle graph `C₁₈` (the Hückel Hamiltonian of the cyclic polyene `C₁₈` in units where
`α = 0`, `β = 1`) if and only if `μ = 2 cos (2πk/18)` for some `k ∈ {0, …, 17}`. -/
