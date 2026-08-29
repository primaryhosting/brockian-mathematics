import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Zeta23Redux.LinAlg

/--
**Rearrangement / Birkhoff step for the von Neumann trace inequality.**

If `S` is a doubly stochastic matrix and `mu`, `nu` are antitone weight sequences, then
`∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i`.

The proof combines two existing Mathlib results:
* `exists_eq_sum_perm_of_mem_doublyStochastic` (Birkhoff's theorem: a doubly stochastic
  matrix is a convex combination of permutation matrices), and
* `Monovary.sum_comp_perm_mul_le_sum_mul` (the rearrangement inequality), together with
  `Antitone.monovary`.
-/
theorem sum_doublyStochastic_mul_le {n : Type*} [Fintype n] [LinearOrder n]
    {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n)
    {mu nu : n → ℝ} (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  -- Entrywise Birkhoff decomposition.
  have hS' : ∀ i j, S i j = ∑ σ : Equiv.Perm n, w σ * (σ.permMatrix ℝ) i j := by
    intro i j
    rw [← hwS]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  -- A permutation matrix picks out a rearrangement of `nu`.
  have hperm : ∀ σ : Equiv.Perm n, ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (mu i * nu j)
      = ∑ i, mu i * nu (σ i) :=
    fun σ => Finset.sum_congr rfl fun i _ => by
      simp [Equiv.toPEquiv_apply, PEquiv.toMatrix_apply]
  -- The rearrangement inequality for the monovarying pair `mu`, `nu`.
  have hrear : ∀ σ : Equiv.Perm n, ∑ i, mu i * nu (σ i) ≤ ∑ i, mu i * nu i := by
    intro σ
    have h := (hmu.monovary hnu).sum_comp_perm_mul_le_sum_mul (σ := σ⁻¹)
    calc ∑ i, mu i * nu (σ i)
        = ∑ i, mu (σ⁻¹ i) * nu i := by
          rw [← Equiv.sum_comp σ (fun i => mu (σ⁻¹ i) * nu i)]; simp
      _ ≤ ∑ i, mu i * nu i := h
  set F : Equiv.Perm n → n → n → ℝ :=
    fun σ i j => w σ * ((σ.permMatrix ℝ) i j * (mu i * nu j)) with hF
  have step1 : ∑ i, ∑ j, S i j * (mu i * nu j) = ∑ i, ∑ j, ∑ σ, F σ i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hS', Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by rw [hF]; ring
  have step2 : ∑ i, ∑ j, ∑ σ, F σ i j = ∑ i, ∑ σ, ∑ j, F σ i j :=
    Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have step3 : ∑ i, ∑ σ, ∑ j, F σ i j = ∑ σ, ∑ i, ∑ j, F σ i j := Finset.sum_comm
  calc ∑ i, ∑ j, S i j * (mu i * nu j)
      = ∑ σ : Equiv.Perm n, ∑ i, ∑ j, F σ i j := by rw [step1, step2, step3]
    _ ≤ ∑ σ : Equiv.Perm n, w σ * ∑ i, mu i * nu i := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have hσ : ∑ i, ∑ j, F σ i j
            = w σ * ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (mu i * nu j) := by
          simp only [hF, Finset.mul_sum]
        rw [hσ, hperm σ]
        exact mul_le_mul_of_nonneg_left (hrear σ) (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

end Zeta23Redux.LinAlg

