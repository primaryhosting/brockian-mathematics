import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
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

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- For a unitary matrix `W`, the matrix of squared norms of the entries of `W` is doubly
stochastic: its rows sum to `1` because `W * Wᴴ = 1`, and its columns sum to `1` because
`Wᴴ * W = 1`. -/

theorem vonNeumann_trace_ineq_hermitian {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    RCLike.re (Matrix.trace (A * B)) ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hVdef
  have hU : U ∈ Matrix.unitaryGroup n 𝕜 := hA.eigenvectorUnitary.2
  have hV : V ∈ Matrix.unitaryGroup n 𝕜 := hB.eigenvectorUnitary.2
  have hA' : A = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [hUdef]
  have hB' : B = V * Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) * star V := by
    conv_lhs => rw [hB.spectral_theorem]
    simp [hVdef]
  have hW : (star U * V) ∈ Matrix.unitaryGroup n 𝕜 := mul_mem (Unitary.star_mem hU) hV
  set M : Matrix n n ℝ := Matrix.of fun j k => ‖(star U * V) j k‖ ^ 2 with hM
  have hMds : M ∈ doublyStochastic ℝ n := unitary_normSq_mem_doublyStochastic hW
  have hMsub : M.submatrix e e ∈ doublyStochastic ℝ (Fin (Fintype.card n)) := by
    have := reindex_mem_doublyStochastic (e₁ := e.symm) (e₂ := e.symm) hMds
    simpa [Matrix.reindex] using this
  have heig : ∀ j, hA.eigenvalues (e j) = hA.eigenvalues₀ j := by
    intro j; simp [he, Matrix.IsHermitian.eigenvalues]
  have heig' : ∀ j, hB.eigenvalues (e j) = hB.eigenvalues₀ j := by
    intro j; simp [he, Matrix.IsHermitian.eigenvalues]
  calc RCLike.re (Matrix.trace (A * B))
      = ∑ j, ∑ k, hA.eigenvalues j * hB.eigenvalues k * ‖(star U * V) j k‖ ^ 2 := by
        conv_lhs => rw [hA', hB']
        exact re_trace_conj_diag hU _ _
    _ = ∑ j, ∑ k, hA.eigenvalues₀ j * hB.eigenvalues₀ k * (M.submatrix e e) j k := by
        rw [← Equiv.sum_comp e (fun j => ∑ k, hA.eigenvalues j * hB.eigenvalues k *
          ‖(star U * V) j k‖ ^ 2)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Equiv.sum_comp e (fun k => hA.eigenvalues (e j) * hB.eigenvalues k *
          ‖(star U * V) (e j) k‖ ^ 2)]
        exact Finset.sum_congr rfl fun k _ => by simp [heig, heig', hM]
    _ ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i :=
        sum_mul_doublyStochastic_le hA.eigenvalues₀_antitone hB.eigenvalues₀_antitone hMsub

end Zeta23Core

