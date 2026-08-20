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

open scoped BigOperators Kronecker ComplexOrder
open Matrix Module

namespace QI

section LinearAlgebra

variable {X W : Type*} [Fintype X] [Fintype W] [DecidableEq X] [DecidableEq W]

/-- Rank factorization: every matrix `F` factors as `U * L * F = F` with `U` having
`F.rank` columns. -/

theorem quantum_singleton_add {k d K : ℕ} {ψ : Fin K → ((Fin n → Fin q) → ℂ)}
    (hq : 2 ≤ q) (hk : 1 ≤ k) (hK : K = q ^ k) (h : IsQECC n q d K ψ) :
    2 * (d - 1) + k ≤ n := by
  classical
  have hK1 : 1 ≤ K := by
    rw [hK]; exact Nat.one_le_pow _ _ (by omega)
  have pow_le : K ≤ q ^ n := card_le_pow h
  have disj_le : ∀ (A B : Finset (Fin n)), Disjoint A B → A.card + 1 ≤ d → B.card + 1 ≤ d →
      K ≤ q ^ (n - A.card - B.card) :=
    fun A B hAB hA hB => card_le_of_disjoint_erasures h hK1 A B hAB hA hB
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Nat.zero_sub, Nat.mul_zero, Nat.zero_add]
    rw [hK] at pow_le
    exact (Nat.pow_le_pow_iff_right hq).mp pow_le
  · rcases Nat.lt_or_ge n (2 * (d - 1)) with hcase | hcase
    · exfalso
      obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (Fin n))) (n := min (d - 1) n) (by simp)
      obtain ⟨B, hBsub, hB⟩ := Finset.exists_subset_card_eq (s := Aᶜ) (n := n - min (d - 1) n)
        (by rw [Finset.card_compl, hA]; simp)
      have hdisj : Disjoint A B :=
        Finset.disjoint_left.mpr fun a haA haB => (Finset.mem_compl.mp (hBsub haB)) haA
      have hle := disj_le A B hdisj (by omega) (by omega)
      rw [hA, hB, hK] at hle
      have h0 : n - min (d - 1) n - (n - min (d - 1) n) = 0 := by omega
      rw [h0, pow_zero] at hle
      have h2 : q ^ 1 ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk
      simp at h2
      omega
    · obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (Fin n))) (n := d - 1) (by simp; omega)
      obtain ⟨B, hBsub, hB⟩ := Finset.exists_subset_card_eq (s := Aᶜ) (n := d - 1)
        (by rw [Finset.card_compl, hA]; simp; omega)
      have hdisj : Disjoint A B :=
        Finset.disjoint_left.mpr fun a haA haB => (Finset.mem_compl.mp (hBsub haB)) haA
      have hle := disj_le A B hdisj (by omega) (by omega)
      rw [hA, hB, hK] at hle
      have hkn : k ≤ n - (d - 1) - (d - 1) := (Nat.pow_le_pow_iff_right hq).mp hle
      omega

/-- **Quantum Singleton bound**: an `[[n, k, d]]` quantum code (with `k ≥ 1` logical qudits,
local dimension `q ≥ 2`) obeys `n - k ≥ 2 * (d - 1)`. -/
