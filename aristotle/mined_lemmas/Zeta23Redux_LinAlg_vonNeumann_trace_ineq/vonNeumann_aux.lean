import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared moduli along a row of a unitary matrix sum to `1`. -/

lemma vonNeumann_aux (U V : Matrix n n ℂ) (hUU : Uᴴ * U = 1) (hUU' : U * Uᴴ = 1)
    (hVV : Vᴴ * V = 1) (hVV' : V * Vᴴ = 1) (lam xi mu nu : n → ℝ) (sA sB : Equiv.Perm n)
    (hmu : mu = lam ∘ sA) (hnu : nu = xi ∘ sB) (hmn : Monovary mu nu) :
    ((U * diagonal (fun i => (lam i : ℂ)) * Uᴴ) *
      (V * diagonal (fun i => (xi i : ℂ)) * Vᴴ)).trace.re ≤ ∑ i, mu i * nu i := by
  set T : Matrix n n ℂ := Uᴴ * V with hTdef
  have hT : Tᴴ = Vᴴ * U := by simp [hTdef, Matrix.conjTranspose_mul]
  have hTT : T * Tᴴ = 1 := by
    rw [hT, hTdef]
    calc Uᴴ * V * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * U := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hVV']; simp [hUU]
  have hTT' : Tᴴ * T = 1 := by
    rw [hT, hTdef]
    calc Vᴴ * U * (Uᴴ * V) = Vᴴ * (U * Uᴴ) * V := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hUU']; simp [hVV]
  have hX : (U * diagonal (fun i => (lam i : ℂ)) * Uᴴ) *
      (V * diagonal (fun i => (xi i : ℂ)) * Vᴴ)
      = U * (diagonal (fun i => (lam i : ℂ)) * (Uᴴ * V) *
          diagonal (fun i => (xi i : ℂ)) * Vᴴ) := by
    simp [Matrix.mul_assoc]
  have hXU : (diagonal (fun i => (lam i : ℂ)) * (Uᴴ * V) *
      diagonal (fun i => (xi i : ℂ)) * Vᴴ) * U
      = diagonal (fun i => (lam i : ℂ)) * T * diagonal (fun i => (xi i : ℂ)) * Tᴴ := by
    rw [hT, hTdef]; simp [Matrix.mul_assoc]
  have htr : ((U * diagonal (fun i => (lam i : ℂ)) * Uᴴ) *
      (V * diagonal (fun i => (xi i : ℂ)) * Vᴴ)).trace
      = ((∑ i, ∑ j, lam i * xi j * ‖T i j‖ ^ 2 : ℝ) : ℂ) := by
    rw [hX, Matrix.trace_mul_comm, hXU, trace_diag_mul_diag]
  rw [htr, Complex.ofReal_re]
  set S : Matrix n n ℝ := Matrix.of fun a b => ‖T (sA a) (sB b)‖ ^ 2 with hSdef
  have hSmem : S ∈ doublyStochastic ℝ n := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun a => ?_, fun b => ?_⟩
    · simp only [hSdef, Matrix.of_apply]
      positivity
    · have := Equiv.sum_comp sB (fun j => ‖T (sA a) j‖ ^ 2)
      simpa [hSdef] using this.trans (sum_sq_norm_row T hTT (sA a))
    · have := Equiv.sum_comp sA (fun i => ‖T i (sB b)‖ ^ 2)
      simpa [hSdef] using this.trans (sum_sq_norm_col T hTT' (sB b))
  have hreindex : ∑ i, ∑ j, lam i * xi j * ‖T i j‖ ^ 2 = ∑ a, ∑ b, mu a * nu b * S a b := by
    rw [← Equiv.sum_comp sA (fun i => ∑ j, lam i * xi j * ‖T i j‖ ^ 2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp sB (fun j => lam (sA a) * xi j * ‖T (sA a) j‖ ^ 2)]
    simp [hmu, hnu, hSdef]
  rw [hreindex]
  exact sum_bilin_le_of_doublyStochastic mu nu hmn S hSmem

/-- **Von Neumann's trace inequality** for Hermitian matrices.
If `mu` and `nu` list the eigenvalues of the Hermitian matrices `A` and `B` respectively,
both in the same (decreasing) order, then `Re (tr (A * B)) ≤ ∑ i, mu i * nu i`. -/
