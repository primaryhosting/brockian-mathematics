/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Zeta23Redux.LinAlg

/-- **Rearrangement against a doubly stochastic matrix.** If `S` is doubly stochastic and
`mu`, `nu` are both antitone, then the bilinear form `∑ i j, mu i * S i j * nu j` is at most
the aligned sum `∑ i, mu i * nu i`.  Proved via Birkhoff's theorem plus the rearrangement
inequality. -/

theorem sum_mul_doublyStochastic_le {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S ∈ doublyStochastic ℝ (Fin d)) {mu nu : Fin d → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, ∑ j, mu i * S i j * nu j ≤ ∑ i, mu i * nu i := by
  have hmn : Monovary mu nu := by
    intro i j hij
    have : j < i := by
      by_contra h
      exact absurd (hnu (not_lt.mp h)) (not_le.mpr hij)
    exact hmu this.le
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have key : ∀ σ : Equiv.Perm (Fin d),
      ∑ i, ∑ j, mu i * (σ.permMatrix ℝ) i j * nu j ≤ ∑ i, mu i * nu i := by
    intro σ
    have hrow : ∀ i, ∑ j, mu i * (σ.permMatrix ℝ) i j * nu j = mu i * nu (σ i) := by
      intro i
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    rw [Finset.sum_congr rfl fun i _ => hrow i]
    simpa using hmn.sum_smul_comp_perm_le_sum_smul (σ := σ)
  calc ∑ i, ∑ j, mu i * S i j * nu j
      = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, ∑ j, mu i * (σ.permMatrix ℝ) i j * nu j := by
        rw [← hwS]
        simp only [Matrix.sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
            Finset.sum_comm (s := (Finset.univ : Finset (Fin d)))
              (t := (Finset.univ : Finset (Equiv.Perm (Fin d))))
              (f := fun j σ => mu i * (w σ * (σ.permMatrix ℝ) i j) * nu j),
          Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu i :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (key σ) (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- The trace of `diagonal a * W * diagonal b * Wᴴ` is the real number
`∑ i j, a i * b j * ‖W i j‖ ^ 2`. -/
