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

theorem card_le_of_two_correctable (M : Matrix (α × β × γ) κ ℂ) (hM : M ≠ 0)
    (σA : Matrix α α ℂ)
    (hA : ∀ (a a' : α) (i j : κ),
      ∑ p : β × γ, (starRingEnd ℂ) (M (a, p.1, p.2) i) * M (a', p.1, p.2) j
        = σA a a' * (if i = j then 1 else 0))
    (σB : Matrix β β ℂ)
    (hB : ∀ (b b' : β) (i j : κ),
      ∑ p : α × γ, (starRingEnd ℂ) (M (p.1, b, p.2) i) * M (p.1, b', p.2) j
        = σB b b' * (if i = j then 1 else 0)) :
    Fintype.card κ ≤ Fintype.card γ := by
  classical
  set NA : Matrix (β × γ) (α × κ) ℂ := Matrix.of fun p q => M (q.1, p.1, p.2) q.2 with hNA
  set NB : Matrix (α × γ) (β × κ) ℂ := Matrix.of fun p q => M (p.1, q.1, p.2) q.2 with hNB
  set FA : Matrix α (β × γ × κ) ℂ := Matrix.of fun a p => M (a, p.1, p.2.1) p.2.2 with hFA
  set FB : Matrix β (α × γ × κ) ℂ := Matrix.of fun b p => M (p.1, b, p.2.1) p.2.2 with hFB
  set FC : Matrix γ (α × β × κ) ℂ := Matrix.of fun c p => M (p.1, p.2.1, c) p.2.2 with hFC
  -- Gram matrices of the two flattenings
  have hgramA : NAᴴ * NA
      = Matrix.of fun p q : α × κ => σA p.1 q.1 * (if p.2 = q.2 then 1 else 0) := by
    ext q q'
    rw [Matrix.mul_apply]
    simpa [Matrix.conjTranspose_apply, hNA] using hA q.1 q'.1 q.2 q'.2
  have hgramB : NBᴴ * NB
      = Matrix.of fun p q : β × κ => σB p.1 q.1 * (if p.2 = q.2 then 1 else 0) := by
    ext q q'
    rw [Matrix.mul_apply]
    simpa [Matrix.conjTranspose_apply, hNB] using hB q.1 q'.1 q.2 q'.2
  have hrankNA : NA.rank = Fintype.card κ * σA.rank := by
    rw [← Matrix.rank_conjTranspose_mul_self NA, hgramA, rank_kron_id]
  have hrankNB : NB.rank = Fintype.card κ * σB.rank := by
    rw [← Matrix.rank_conjTranspose_mul_self NB, hgramB, rank_kron_id]
  -- Tucker bounds
  have htA : NA.rank ≤ FB.rank * FC.rank := by
    refine le_trans (tucker_rank_le NA) ?_
    have h1 : (Matrix.of fun (b : β) (p : γ × (α × κ)) => NA (b, p.1) p.2)
        = FB.submatrix (Equiv.refl β) (swap12 γ α κ) := rfl
    have h2 : (Matrix.of fun (c : γ) (p : β × (α × κ)) => NA (p.1, c) p.2)
        = FC.submatrix (Equiv.refl γ) (swap12 β α κ) := rfl
    rw [h1, h2, Matrix.rank_submatrix FB (Equiv.refl β) (swap12 γ α κ),
      Matrix.rank_submatrix FC (Equiv.refl γ) (swap12 β α κ)]
  have htB : NB.rank ≤ FA.rank * FC.rank := by
    refine le_trans (tucker_rank_le NB) ?_
    have h1 : (Matrix.of fun (a : α) (p : γ × (β × κ)) => NB (a, p.1) p.2)
        = FA.submatrix (Equiv.refl α) (swap12 γ β κ) := rfl
    have h2 : (Matrix.of fun (c : γ) (p : α × (β × κ)) => NB (p.1, c) p.2) = FC := rfl
    rw [h1, h2, Matrix.rank_submatrix FA (Equiv.refl α) (swap12 γ β κ)]
  -- The mode ranks are bounded by the ranks of the reduced densities
  have hFAle : FA.rank ≤ σA.rank := by
    have hkey : FA * FAᴴ = ((Fintype.card κ : ℂ) • (1 : Matrix α α ℂ)) * σAᵀ := by
      ext a a'
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have hr : ∑ a'', ((Fintype.card κ : ℂ) • (1 : Matrix α α ℂ)) a a'' * σAᵀ a'' a'
          = (Fintype.card κ : ℂ) * σA a' a := by
        simp [Matrix.one_apply, Matrix.transpose_apply, Finset.sum_ite_eq]
      rw [hr]
      have hl : ∑ p : β × γ × κ, FA a p * (FAᴴ) p a'
          = ∑ i : κ, ∑ p : β × γ, (starRingEnd ℂ) (M (a', p.1, p.2) i) * M (a, p.1, p.2) i := by
        simp only [hFA, Matrix.of_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
        calc ∑ b : β, ∑ c : γ, ∑ i : κ, M (a, b, c) i * (starRingEnd ℂ) (M (a', b, c) i)
            = ∑ b : β, ∑ i : κ, ∑ c : γ, M (a, b, c) i * (starRingEnd ℂ) (M (a', b, c) i) :=
              Finset.sum_congr rfl fun b _ => Finset.sum_comm
          _ = ∑ i : κ, ∑ b : β, ∑ c : γ, M (a, b, c) i * (starRingEnd ℂ) (M (a', b, c) i) :=
              Finset.sum_comm
          _ = ∑ i : κ, ∑ b : β, ∑ c : γ,
                (starRingEnd ℂ) (M (a', b, c) i) * M (a, b, c) i := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ =>
                Finset.sum_congr rfl fun c _ => by ring
      rw [hl]
      simp_rw [hA a' a]
      simp
    calc FA.rank = (FA * FAᴴ).rank := (Matrix.rank_self_mul_conjTranspose FA).symm
      _ = (((Fintype.card κ : ℂ) • (1 : Matrix α α ℂ)) * σAᵀ).rank := by rw [hkey]
      _ ≤ (σAᵀ).rank := Matrix.rank_mul_le_right _ _
      _ = σA.rank := Matrix.rank_transpose σA
  have hFBle : FB.rank ≤ σB.rank := by
    have hkey : FB * FBᴴ = ((Fintype.card κ : ℂ) • (1 : Matrix β β ℂ)) * σBᵀ := by
      ext b b'
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have hr : ∑ b'', ((Fintype.card κ : ℂ) • (1 : Matrix β β ℂ)) b b'' * σBᵀ b'' b'
          = (Fintype.card κ : ℂ) * σB b' b := by
        simp [Matrix.one_apply, Matrix.transpose_apply, Finset.sum_ite_eq]
      rw [hr]
      have hl : ∑ p : α × γ × κ, FB b p * (FBᴴ) p b'
          = ∑ i : κ, ∑ p : α × γ, (starRingEnd ℂ) (M (p.1, b', p.2) i) * M (p.1, b, p.2) i := by
        simp only [hFB, Matrix.of_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
        calc ∑ a : α, ∑ c : γ, ∑ i : κ, M (a, b, c) i * (starRingEnd ℂ) (M (a, b', c) i)
            = ∑ a : α, ∑ i : κ, ∑ c : γ, M (a, b, c) i * (starRingEnd ℂ) (M (a, b', c) i) :=
              Finset.sum_congr rfl fun a _ => Finset.sum_comm
          _ = ∑ i : κ, ∑ a : α, ∑ c : γ, M (a, b, c) i * (starRingEnd ℂ) (M (a, b', c) i) :=
              Finset.sum_comm
          _ = ∑ i : κ, ∑ a : α, ∑ c : γ,
                (starRingEnd ℂ) (M (a, b', c) i) * M (a, b, c) i := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
                Finset.sum_congr rfl fun c _ => by ring
      rw [hl]
      simp_rw [hB b' b]
      simp
    calc FB.rank = (FB * FBᴴ).rank := (Matrix.rank_self_mul_conjTranspose FB).symm
      _ = (((Fintype.card κ : ℂ) • (1 : Matrix β β ℂ)) * σBᵀ).rank := by rw [hkey]
      _ ≤ (σBᵀ).rank := Matrix.rank_mul_le_right _ _
      _ = σB.rank := Matrix.rank_transpose σB
  -- positivity of the mode ranks
  have hFAne : FA ≠ 0 := by
    intro h0
    apply hM
    ext p i
    obtain ⟨a, b, c⟩ := p
    have := congrFun (congrFun h0 a) (b, c, i)
    simpa [hFA] using this
  have hFBne : FB ≠ 0 := by
    intro h0
    apply hM
    ext p i
    obtain ⟨a, b, c⟩ := p
    have := congrFun (congrFun h0 b) (a, c, i)
    simpa [hFB] using this
  have hFApos : 1 ≤ FA.rank := rank_pos_of_ne_zero _ hFAne
  have hFBpos : 1 ≤ FB.rank := rank_pos_of_ne_zero _ hFBne
  -- put everything together
  set K := Fintype.card κ
  have e1 : K * FA.rank ≤ FB.rank * FC.rank := by
    calc K * FA.rank ≤ K * σA.rank := Nat.mul_le_mul_left _ hFAle
      _ = NA.rank := hrankNA.symm
      _ ≤ FB.rank * FC.rank := htA
  have e2 : K * FB.rank ≤ FA.rank * FC.rank := by
    calc K * FB.rank ≤ K * σB.rank := Nat.mul_le_mul_left _ hFBle
      _ = NB.rank := hrankNB.symm
      _ ≤ FA.rank * FC.rank := htB
  have e3 : (K * K) * (FA.rank * FB.rank) ≤ (FC.rank * FC.rank) * (FA.rank * FB.rank) := by
    have := Nat.mul_le_mul e1 e2
    calc (K * K) * (FA.rank * FB.rank) = (K * FA.rank) * (K * FB.rank) := by ring
      _ ≤ (FB.rank * FC.rank) * (FA.rank * FC.rank) := this
      _ = (FC.rank * FC.rank) * (FA.rank * FB.rank) := by ring
  have hpos : 0 < FA.rank * FB.rank := Nat.mul_pos hFApos hFBpos
  have e4 : K * K ≤ FC.rank * FC.rank := Nat.le_of_mul_le_mul_right e3 hpos
  have e5 : K ≤ FC.rank := Nat.mul_self_le_mul_self_iff.mp e4
  exact le_trans e5 (Matrix.rank_le_card_height FC)

end Core

/-! ## Quantum codes: the Knill–Laflamme distance condition and the Singleton bound -/

section Codes

variable {n a b c q K : ℕ}

/-- `glue e P` assembles a full string of `n` letters out of the three partial strings `P`,
along the splitting `e` of the coordinate set into three blocks. -/
