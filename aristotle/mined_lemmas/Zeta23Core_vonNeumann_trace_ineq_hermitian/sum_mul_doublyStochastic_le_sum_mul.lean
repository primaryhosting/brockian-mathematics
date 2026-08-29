/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`, so the header above is
-- written as a plain block comment; it is repeated verbatim as a module docstring below.)

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

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of `Dₐ W D_b Wᴴ`, for diagonal matrices with real entries `a`, `b`, expands as
`∑ j k, a j * b k * ‖W j k‖ ^ 2`. -/

theorem sum_mul_doublyStochastic_le_sum_mul {N : ℕ} (e : Fin N ≃ n)
    (f g : Fin N → ℝ) (hf : Antitone f) (hg : Antitone g)
    {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n) :
    ∑ j, ∑ k, f (e.symm j) * g (e.symm k) * S j k ≤ ∑ i, f i * g i := by
  have hmono : Monovary f g := by
    intro i j hij
    exact hf (le_of_not_ge fun h => absurd (hg h) (not_le.2 hij))
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have key : ∀ σ : Equiv.Perm n,
      ∑ j, ∑ k, f (e.symm j) * g (e.symm k) * (σ.permMatrix ℝ) j k ≤ ∑ i, f i * g i := by
    intro σ
    have h1 : ∀ j : n, ∑ k, f (e.symm j) * g (e.symm k) * (σ.permMatrix ℝ) j k
        = f (e.symm j) * g (e.symm (σ j)) := by
      intro j
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    rw [Finset.sum_congr rfl fun j _ => h1 j,
      ← Equiv.sum_comp e (fun j => f (e.symm j) * g (e.symm (σ j)))]
    simp only [Equiv.symm_apply_apply]
    exact hmono.sum_mul_comp_perm_le_sum_mul (σ := (e.trans σ).trans e.symm)
  have hSeq : ∀ j k, S j k = ∑ σ : Equiv.Perm n, w σ * (σ.permMatrix ℝ) j k := by
    intro j k
    rw [← hwS]
    simp [Matrix.sum_apply]
  have hswap : ∀ j : n, ∑ k, ∑ σ : Equiv.Perm n,
      f (e.symm j) * g (e.symm k) * (w σ * (σ.permMatrix ℝ) j k)
      = ∑ σ : Equiv.Perm n, ∑ k, w σ * (f (e.symm j) * g (e.symm k) * (σ.permMatrix ℝ) j k) := by
    intro j
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun k _ => by ring
  calc ∑ j, ∑ k, f (e.symm j) * g (e.symm k) * S j k
      = ∑ σ : Equiv.Perm n, w σ *
          (∑ j, ∑ k, f (e.symm j) * g (e.symm k) * (σ.permMatrix ℝ) j k) := by
        simp only [hSeq, Finset.mul_sum]
        rw [Finset.sum_congr rfl fun j _ => hswap j, Finset.sum_comm]
    _ ≤ ∑ σ : Equiv.Perm n, w σ * (∑ i, f i * g i) :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (key σ) (hw0 σ)
    _ = ∑ i, f i * g i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **Von Neumann trace inequality, Hermitian case.**
For Hermitian matrices `A`, `B` over an `RCLike` field, indexed by a finite type,
`Re (tr (A * B)) ≤ ∑ i, aᵢ * bᵢ`, where `a` and `b` are the eigenvalues of `A` and `B`,
each listed in decreasing order (`Matrix.IsHermitian.eigenvalues₀`). -/
