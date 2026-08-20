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

theorem card_le_of_disjoint_erasures {d K : ℕ} {ψ : Fin K → ((Fin n → Fin q) → ℂ)}
    (h : IsQECC n q d K ψ) (hK : 1 ≤ K) (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hA : A.card + 1 ≤ d) (hB : B.card + 1 ≤ d) :
    K ≤ q ^ (n - A.card - B.card) := by
  classical
  obtain ⟨horth, hkl⟩ := h
  obtain ⟨ρ, hρ⟩ := hkl A hA
  obtain ⟨σ, hσ⟩ := hkl B hB
  set ψ' : Fin K → (({i // i ∈ A} → Fin q) × ({i // i ∈ B} → Fin q) ×
      ({i : Fin n // i ∉ A ∧ i ∉ B} → Fin q)) → ℂ :=
    fun i p => ψ i (merge3 A B p.1 p.2.1 p.2.2) with hψ'
  have hA' : ∀ i j a a', ∑ b, ∑ c, ψ' i (a, b, c) * (starRingEnd ℂ) (ψ' j (a', b, c))
      = (if i = j then (1 : ℂ) else 0) * ρ a a' := by
    intro i j a a'
    calc ∑ b, ∑ c, ψ' i (a, b, c) * (starRingEnd ℂ) (ψ' j (a', b, c))
        = ∑ p : ({i // i ∈ B} → Fin q) × ({i : Fin n // i ∉ A ∧ i ∉ B} → Fin q),
            ψ' i (a, p.1, p.2) * (starRingEnd ℂ) (ψ' j (a', p.1, p.2)) := by
          rw [Fintype.sum_prod_type]
      _ = ∑ p, (fun z => ψ i (merge A a z) * (starRingEnd ℂ) (ψ j (merge A a' z)))
            (eA A B hAB p) :=
          Finset.sum_congr rfl fun p _ => by
            simp only [hψ', merge_eA A B hAB a p.1 p.2, merge_eA A B hAB a' p.1 p.2]
      _ = ∑ z, ψ i (merge A a z) * (starRingEnd ℂ) (ψ j (merge A a' z)) :=
          Equiv.sum_comp (eA A B hAB)
            (fun z => ψ i (merge A a z) * (starRingEnd ℂ) (ψ j (merge A a' z)))
      _ = (if i = j then (1 : ℂ) else 0) * ρ a a' := hρ i j a a'
  have hB' : ∀ i j b b', ∑ a, ∑ c, ψ' i (a, b, c) * (starRingEnd ℂ) (ψ' j (a, b', c))
      = (if i = j then (1 : ℂ) else 0) * σ b b' := by
    intro i j b b'
    calc ∑ a, ∑ c, ψ' i (a, b, c) * (starRingEnd ℂ) (ψ' j (a, b', c))
        = ∑ p : ({i // i ∈ A} → Fin q) × ({i : Fin n // i ∉ A ∧ i ∉ B} → Fin q),
            ψ' i (p.1, b, p.2) * (starRingEnd ℂ) (ψ' j (p.1, b', p.2)) := by
          rw [Fintype.sum_prod_type]
      _ = ∑ p, (fun z => ψ i (merge B b z) * (starRingEnd ℂ) (ψ j (merge B b' z)))
            (eB A B hAB p) :=
          Finset.sum_congr rfl fun p _ => by
            simp only [hψ', merge_eB A B hAB p.1 b p.2, merge_eB A B hAB p.1 b' p.2]
      _ = ∑ z, ψ i (merge B b z) * (starRingEnd ℂ) (ψ j (merge B b' z)) :=
          Equiv.sum_comp (eB A B hAB)
            (fun z => ψ i (merge B b z) * (starRingEnd ℂ) (ψ j (merge B b' z)))
      _ = (if i = j then (1 : ℂ) else 0) * σ b b' := hσ i j b b'
  have hne : ∃ i v, ψ' i v ≠ 0 := by
    set i0 : Fin K := ⟨0, hK⟩
    have h1 := horth i0 i0
    rw [if_pos rfl] at h1
    have hv : ∃ v, ψ i0 v ≠ 0 := by
      by_contra hc
      push_neg at hc
      simp [hc] at h1
    obtain ⟨v, hv⟩ := hv
    refine ⟨i0, (fun j => v j, fun j => v j, fun j => v j), ?_⟩
    have hm : merge3 A B (fun j : {i // i ∈ A} => v j) (fun j : {i // i ∈ B} => v j)
        (fun j : {i : Fin n // i ∉ A ∧ i ∉ B} => v j) = v := by
      funext i
      by_cases h : i ∈ A
      · simp [merge3, h]
      · by_cases h' : i ∈ B <;> simp [merge3, h, h']
    simpa [hψ', hm] using hv
  have hcard : Fintype.card ({i : Fin n // i ∉ A ∧ i ∉ B} → Fin q)
      = q ^ (n - A.card - B.card) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype]
    congr 1
    have hf : (Finset.univ.filter fun i : Fin n => i ∉ A ∧ i ∉ B) = (A ∪ B)ᶜ := by ext i; simp
    rw [hf, Finset.card_compl, Finset.card_union_of_disjoint hAB, Fintype.card_fin]
    omega
  have hfin := core_bound ψ' ρ σ hA' hB' hne
  rwa [hcard] at hfin

/-- The number of codewords of a code on `n` qudits of local dimension `q` is at most `q ^ n`. -/
