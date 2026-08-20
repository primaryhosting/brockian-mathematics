/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Module Kronecker ComplexOrder

namespace QI

/-! ## Linear algebra preliminaries -/

/-- Swap the first two factors of a triple product type. -/

theorem tucker_rank_le {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    {X : Type*} [Fintype X] [DecidableEq X] (T : Matrix (β × γ) X ℂ) :
    T.rank ≤ (Matrix.of fun (b : β) (p : γ × X) => T (b, p.1) p.2).rank *
             (Matrix.of fun (c : γ) (p : β × X) => T (p.1, c) p.2).rank := by
  classical
  obtain ⟨PB, RB, hB⟩ := exists_rank_proj (Matrix.of fun (b : β) (p : γ × X) => T (b, p.1) p.2)
  obtain ⟨PC, RC, hC⟩ := exists_rank_proj (Matrix.of fun (c : γ) (p : β × X) => T (p.1, c) p.2)
  have hBe : ∀ (b : β) (c : γ) (x : X), ∑ b', (PB * RB) b b' * T (b', c) x = T (b, c) x := by
    intro b c x
    have := congrFun (congrFun hB b) (c, x)
    simpa [Matrix.mul_apply] using this
  have hCe : ∀ (b : β) (c : γ) (x : X), ∑ c', (PC * RC) c c' * T (b, c') x = T (b, c) x := by
    intro b c x
    have := congrFun (congrFun hC c) (b, x)
    simpa [Matrix.mul_apply] using this
  have key : ((PB * RB) ⊗ₖ (PC * RC)) * T = T := by
    ext p x
    obtain ⟨b, c⟩ := p
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have h1 : ∀ b' : β, ∑ c', ((PB * RB) ⊗ₖ (PC * RC)) (b, c) (b', c') * T (b', c') x
        = ∑ c', (PB * RB) b b' * ((PC * RC) c c' * T (b', c') x) := by
      intro b'; refine Finset.sum_congr rfl fun c' _ => ?_
      rw [Matrix.kronecker_apply]; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ c' : γ, ∑ b', (PB * RB) b b' * ((PC * RC) c c' * T (b', c') x)
        = (PC * RC) c c' * T (b, c') x := by
      intro c'
      rw [← hBe b c' x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b' _ => by ring
    simp_rw [h2]
    exact hCe b c x
  calc T.rank = (((PB * RB) ⊗ₖ (PC * RC)) * T).rank := by rw [key]
    _ ≤ ((PB * RB) ⊗ₖ (PC * RC)).rank := Matrix.rank_mul_le_left _ _
    _ = ((PB ⊗ₖ PC) * (RB ⊗ₖ RC)).rank := by rw [Matrix.mul_kronecker_mul]
    _ ≤ (PB ⊗ₖ PC).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin _ × Fin _) := Matrix.rank_le_card_width _
    _ = _ := by simp

/-- The rank of `σ ⊗ 1` is `card κ` times the rank of `σ`. -/
