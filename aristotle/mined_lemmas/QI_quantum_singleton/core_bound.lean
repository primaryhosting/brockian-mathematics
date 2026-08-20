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

theorem core_bound {K : ℕ} (ψ : Fin K → α × β × γ → ℂ) (ρ : Matrix α α ℂ) (σ : Matrix β β ℂ)
    (hA : ∀ i j a a', ∑ b : β, ∑ c : γ, ψ i (a, b, c) * (starRingEnd ℂ) (ψ j (a', b, c))
        = (if i = j then (1 : ℂ) else 0) * ρ a a')
    (hB : ∀ i j b b', ∑ a : α, ∑ c : γ, ψ i (a, b, c) * (starRingEnd ℂ) (ψ j (a, b', c))
        = (if i = j then (1 : ℂ) else 0) * σ b b')
    (hne : ∃ i v, ψ i v ≠ 0) :
    K ≤ Fintype.card γ := by
  classical
  obtain ⟨i0, ⟨a0, b0, c0⟩, hv0⟩ := hne
  have hK : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · exact absurd i0.isLt (by omega)
    · exact h
  have hKC : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- the reduced operators are nonzero
  have hnorm : ∀ (i : Fin K) (a : α), ∀ b c, ρ a a = 0 → ψ i (a, b, c) = 0 := by
    intro i a b c hρ0
    have hd := hA i i a a
    rw [if_pos rfl, one_mul, hρ0] at hd
    have hsum : ∑ b' : β, ∑ c' : γ, Complex.normSq (ψ i (a, b', c')) = 0 := by
      have hC : ((∑ b' : β, ∑ c' : γ, Complex.normSq (ψ i (a, b', c')) : ℝ) : ℂ) = 0 := by
        push_cast
        simp_rw [← Complex.mul_conj]
        rw [hd]
      exact_mod_cast hC
    have hnn : ∀ b' ∈ Finset.univ, (0 : ℝ) ≤ ∑ c' : γ, Complex.normSq (ψ i (a, b', c')) :=
        fun b' _ => Finset.sum_nonneg fun c' _ => Complex.normSq_nonneg _
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum b (Finset.mem_univ b)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun c' _ => Complex.normSq_nonneg (ψ i (a, b, c')))).mp h1 c (Finset.mem_univ c)
    simpa [Complex.normSq_eq_zero] using h2
  have hρ : ρ ≠ 0 := by
    intro hρ0
    exact hv0 (hnorm i0 a0 b0 c0 (by rw [hρ0]; rfl))
  have hnormB : ∀ (i : Fin K) (b : β), ∀ a c, σ b b = 0 → ψ i (a, b, c) = 0 := by
    intro i b a c hσ0
    have hd := hB i i b b
    rw [if_pos rfl, one_mul, hσ0] at hd
    have hsum : ∑ a' : α, ∑ c' : γ, Complex.normSq (ψ i (a', b, c')) = 0 := by
      have hC : ((∑ a' : α, ∑ c' : γ, Complex.normSq (ψ i (a', b, c')) : ℝ) : ℂ) = 0 := by
        push_cast
        simp_rw [← Complex.mul_conj]
        rw [hd]
      exact_mod_cast hC
    have hnn : ∀ a' ∈ Finset.univ, (0 : ℝ) ≤ ∑ c' : γ, Complex.normSq (ψ i (a', b, c')) :=
      fun a' _ => Finset.sum_nonneg fun c' _ => Complex.normSq_nonneg _
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum a (Finset.mem_univ a)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun c' _ => Complex.normSq_nonneg (ψ i (a, b, c')))).mp h1 c (Finset.mem_univ c)
    simpa [Complex.normSq_eq_zero] using h2
  have hσ : σ ≠ 0 := by
    intro hσ0
    exact hv0 (hnormB i0 b0 a0 c0 (by rw [hσ0]; rfl))
  -- the various flattenings of the code
  set M : Matrix (Fin K × α) (β × γ) ℂ := Matrix.of fun p r => ψ p.1 (p.2, r.1, r.2) with hM
  set N : Matrix (Fin K × β) (α × γ) ℂ := Matrix.of fun p r => ψ p.1 (r.1, p.2, r.2) with hN
  set FA : Matrix α (Fin K × β × γ) ℂ := Matrix.of fun a r => ψ r.1 (a, r.2.1, r.2.2) with hFA
  set FB : Matrix β (Fin K × α × γ) ℂ := Matrix.of fun b r => ψ r.1 (r.2.1, b, r.2.2) with hFB
  set FC : Matrix γ (Fin K × α × β) ℂ := Matrix.of fun c r => ψ r.1 (r.2.1, r.2.2, c) with hFC
  have hMM : M * Mᴴ = (1 : Matrix (Fin K) (Fin K) ℂ) ⊗ₖ ρ := by
    ext p p'
    obtain ⟨i, a⟩ := p; obtain ⟨j, a'⟩ := p'
    simp only [hM, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, RCLike.star_def]
    rw [hA i j a a']
  have hNN : N * Nᴴ = (1 : Matrix (Fin K) (Fin K) ℂ) ⊗ₖ σ := by
    ext p p'
    obtain ⟨i, b⟩ := p; obtain ⟨j, b'⟩ := p'
    simp only [hN, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, RCLike.star_def]
    rw [hB i j b b']
  have hFAA : FA * FAᴴ = (K : ℂ) • ρ := by
    ext a a'
    simp only [hFA, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, RCLike.star_def]
    rw [Finset.sum_congr rfl fun i _ => hA i i a a']
    simp
  have hFBB : FB * FBᴴ = (K : ℂ) • σ := by
    ext b b'
    simp only [hFB, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, RCLike.star_def]
    rw [Finset.sum_congr rfl fun i _ => hB i i b b']
    simp
  have hrM : M.rank = K * ρ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose M, hMM, rank_one_kronecker]
  have hrN : N.rank = K * σ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose N, hNN, rank_one_kronecker]
  have hrFA : FA.rank = ρ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose FA, hFAA, rank_smul_of_ne_zero hKC]
  have hrFB : FB.rank = σ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose FB, hFBB, rank_smul_of_ne_zero hKC]
  -- rank subadditivity applied to the two bipartitions
  have flat1 := rank_flatten_le (fun (b : β) (c : γ) (p : Fin K × α) => ψ p.1 (p.2, b, c))
  have flat2 := rank_flatten_le (fun (a : α) (c : γ) (p : Fin K × β) => ψ p.1 (a, p.2, c))
  have e1 : (Matrix.of fun (p : β × γ) (z : Fin K × α) => ψ z.1 (z.2, p.1, p.2)) = Mᵀ := by
    rw [hM]; rfl
  have e2 : (Matrix.of fun (b : β) (p : γ × (Fin K × α)) => ψ p.2.1 (p.2.2, b, p.1))
      = FB.submatrix ⇑(Equiv.refl β) ⇑(swapEquiv γ (Fin K) α) := by rw [hFB]; rfl
  have e3 : (Matrix.of fun (c : γ) (p : β × (Fin K × α)) => ψ p.2.1 (p.2.2, p.1, c))
      = FC.submatrix ⇑(Equiv.refl γ) ⇑(swapEquiv β (Fin K) α) := by rw [hFC]; rfl
  have e4 : (Matrix.of fun (p : α × γ) (z : Fin K × β) => ψ z.1 (p.1, z.2, p.2)) = Nᵀ := by
    rw [hN]; rfl
  have e5 : (Matrix.of fun (a : α) (p : γ × (Fin K × β)) => ψ p.2.1 (a, p.2.2, p.1))
      = FA.submatrix ⇑(Equiv.refl α) ⇑(swapEquiv γ (Fin K) β) := by rw [hFA]; rfl
  have e6 : (Matrix.of fun (c : γ) (p : α × (Fin K × β)) => ψ p.2.1 (p.1, p.2.2, c))
      = FC.submatrix ⇑(Equiv.refl γ) ⇑(shuffleEquiv α (Fin K) β) := by rw [hFC]; rfl
  rw [e1, e2, e3, Matrix.rank_transpose, Matrix.rank_submatrix, Matrix.rank_submatrix,
    hrM, hrFB] at flat1
  rw [e4, e5, e6, Matrix.rank_transpose, Matrix.rank_submatrix, Matrix.rank_submatrix,
    hrN, hrFA] at flat2
  have ha : 1 ≤ ρ.rank := one_le_rank_of_ne_zero ρ hρ
  have hb : 1 ≤ σ.rank := one_le_rank_of_ne_zero σ hσ
  have hsq : (K * K) * (ρ.rank * σ.rank) ≤ (FC.rank * FC.rank) * (ρ.rank * σ.rank) := by
    calc (K * K) * (ρ.rank * σ.rank) = (K * ρ.rank) * (K * σ.rank) := by ring
      _ ≤ (σ.rank * FC.rank) * (ρ.rank * FC.rank) := Nat.mul_le_mul flat1 flat2
      _ = (FC.rank * FC.rank) * (ρ.rank * σ.rank) := by ring
  have hKK : K * K ≤ FC.rank * FC.rank :=
    Nat.le_of_mul_le_mul_right hsq (Nat.mul_pos ha hb)
  have hKc : K ≤ FC.rank := by nlinarith
  exact hKc.trans (Matrix.rank_le_card_height FC)

end Core

section Code

variable {n q : ℕ}

/-- Glue a configuration on `S` and a configuration on the complement of `S` into a global
configuration of `n` qudits. -/
