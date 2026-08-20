import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

/-- Birkhoff + rearrangement: for antitone `mu`, `nu` and a doubly stochastic matrix `S`,
the bilinear form `∑ i j, S i j * (mu i * nu j)` is at most `∑ i, mu i * nu i`. -/

theorem vonNeumann_trace_ineq {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {mu nu : Fin d → ℝ}
    {eA eB : Equiv.Perm (Fin d)} (hmuA : mu = hA.eigenvalues ∘ eA)
    (hnuB : nu = hB.eigenvalues ∘ eB) (hmu : Antitone mu) (hnu : Antitone nu) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
    with hUdef
  set V : Matrix (Fin d) (Fin d) ℂ := (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
    with hVdef
  set Dmu : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) with hDmu
  set Dnu : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) with hDnu
  have hAeq : A = U * Dmu * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [hUdef, hDmu, Function.comp_def]
  have hBeq : B = V * Dnu * star V := by
    conv_lhs => rw [hB.spectral_theorem]
    simp [hVdef, hDnu, Function.comp_def]
  set W : Matrix (Fin d) (Fin d) ℂ := star U * V with hWdef
  have hWmem : W ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [hWdef, hUdef, hVdef]
    exact Submonoid.mul_mem _ (Unitary.star_mem hA.eigenvectorUnitary.2)
      hB.eigenvectorUnitary.2
  have hWstar : Wᴴ = star V * U := by
    rw [← Matrix.star_eq_conjTranspose, hWdef, Matrix.star_mul, star_star]
  -- rewrite the trace
  have htr : Matrix.trace (A * B) = Matrix.trace (Dmu * W * Dnu * Wᴴ) := by
    rw [hWstar, hWdef, hAeq, hBeq]
    rw [show U * Dmu * star U * (V * Dnu * star V)
        = U * (Dmu * star U * V * Dnu * star V) from by simp only [mul_assoc]]
    rw [Matrix.trace_mul_comm]
    congr 1
    simp only [mul_assoc]
  rw [htr, trace_diagonal_mul_mul_diagonal_mul_conjTranspose, Complex.ofReal_re]
  -- reindex the doubly stochastic matrix
  set S : Matrix (Fin d) (Fin d) ℝ :=
    (Matrix.of fun i j => ‖W i j‖ ^ 2).reindex eA.symm eB.symm with hSdef
  have hSmem : S ∈ doublyStochastic ℝ (Fin d) :=
    reindex_mem_doublyStochastic (sq_abs_mem_doublyStochastic hWmem)
  have hSapply : ∀ i j, S i j = ‖W (eA i) (eB j)‖ ^ 2 := by
    intro i j; simp [hSdef]
  have hreindex : ∑ i, ∑ j, ‖W i j‖ ^ 2 * (hA.eigenvalues i * hB.eigenvalues j)
      = ∑ i, ∑ j, S i j * (mu i * nu j) := by
    rw [← Equiv.sum_comp eA (fun i => ∑ j, ‖W i j‖ ^ 2 * (hA.eigenvalues i * hB.eigenvalues j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp eB
      (fun j => ‖W (eA i) j‖ ^ 2 * (hA.eigenvalues (eA i) * hB.eigenvalues j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hSapply, hmuA, hnuB]
    rfl
  rw [hreindex]
  exact sum_bilinear_le_of_mem_doublyStochastic hmu hnu hSmem

/-- Existential form of **von Neumann's trace inequality**: for Hermitian `A`, `B` there exist
listings `mu`, `nu` of their eigenvalues, both in decreasing order, with
`Re (trace (A * B)) ≤ ∑ i, mu i * nu i`. -/
