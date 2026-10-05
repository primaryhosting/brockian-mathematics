import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/

lemma C3adjC_mulVec_blochMO (k : Fin 3) :
    C3adjC.mulVec (blochMO k)
      = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) : ℝ) : ℂ) • blochMO k := by
  funext j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, C3adjC, blochMO,
      C3_cos_one, C3_cos_two] <;>
    (try simp only [omega3_exp_one, omega3_exp_two, omega3_exp_four]) <;>
    first
      | linear_combination omega3_quad
      | linear_combination -omega3_quad
      | norm_num

/-- **Hückel theory for cyclopropenyl (`C₃`).**
The adjacency (Hückel) eigenvalues of the cycle graph `C₃` are exactly the numbers
`2 cos (2πk/3)` for `k = 0, 1, 2`:

* the characteristic polynomial factors as `∏ k, (X - 2 cos (2πk/3))`, so these are the
  eigenvalues counted with multiplicity (namely `2, -1, -1`);
* a real number `μ` admits a nonzero eigenvector iff `μ = 2 cos (2πk/3)` for some `k`;
* for each `k`, the Bloch vector `(exp(2πi k j/3))_j` is a nonzero eigenvector with
  eigenvalue `2 cos (2πk/3)`. -/
