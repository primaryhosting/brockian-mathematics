import Mathlib

/-!
Rank tools and the core decoupling lemma behind the quantum Singleton bound.
-/

open Matrix Module
open scoped ComplexOrder

namespace QI

variable {X Y Z R : Type*}

section RankTools

/-- Vectors on `Z × X` all of whose `Z`-slices lie in `W`. -/

theorem card_le_of_decoupled [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (f : R → A → B → C → ℂ) (σ : Matrix A A ℂ) (τ : Matrix B B ℂ)
    (hA : ∀ i j a a', (∑ c, ∑ b, f i a b c * conj (f j a' b c))
            = (if i = j then (1 : ℂ) else 0) * σ a a')
    (hB : ∀ i j b b', (∑ c, ∑ a, f i a b c * conj (f j a b' c))
            = (if i = j then (1 : ℂ) else 0) * τ b b')
    (hf : ∃ i a b c, f i a b c ≠ 0) :
    Fintype.card R ≤ Fintype.card C := by
  classical
  obtain ⟨i₀, a₀, b₀, c₀, hne⟩ := hf
  have hRpos : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨i₀⟩
  -- the four reshapings
  set MRA : Matrix (R × A) (C × B) ℂ := fun p r => f p.1 p.2 r.2 r.1 with hMRA
  set MRB : Matrix (R × B) (C × A) ℂ := fun p r => f p.1 r.2 p.2 r.1 with hMRB
  set MA : Matrix A (C × (R × B)) ℂ := fun a p => f p.2.1 a p.2.2 p.1 with hMA
  set MB : Matrix B (C × (R × A)) ℂ := fun b p => f p.2.1 p.2.2 b p.1 with hMB
  -- rank of MRA
  have hMRArank : MRA.rank = Fintype.card R * σ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose MRA]
    refine rank_id_tensor σ _ ?_
    intro i j a a'
    have : (MRA * MRAᴴ) (i, a) (j, a') = ∑ r : C × B, f i a r.2 r.1 * conj (f j a' r.2 r.1) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hMRA]
    rw [this, Fintype.sum_prod_type]
    exact hA i j a a'
  have hMRBrank : MRB.rank = Fintype.card R * τ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose MRB]
    refine rank_id_tensor τ _ ?_
    intro i j b b'
    have : (MRB * MRBᴴ) (i, b) (j, b') = ∑ r : C × A, f i r.2 b r.1 * conj (f j r.2 b' r.1) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hMRB]
    rw [this, Fintype.sum_prod_type]
    exact hB i j b b'
  -- rank of the single-party reshapings
  have hMArank : MA.rank = σ.rank := by
    have hprod : MA * MAᴴ = (Fintype.card R : ℂ) • σ := by
      ext a a'
      have h1 : (MA * MAᴴ) a a'
          = ∑ p : C × (R × B), f p.2.1 a p.2.2 p.1 * conj (f p.2.1 a' p.2.2 p.1) := by
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hMA]
      rw [h1, Fintype.sum_prod_type]
      have h2 : ∀ c : C, (∑ p : R × B, f p.1 a p.2 c * conj (f p.1 a' p.2 c))
          = ∑ i : R, ∑ b : B, f i a b c * conj (f i a' b c) := by
        intro c; rw [Fintype.sum_prod_type]
      simp only [h2]
      rw [Finset.sum_comm]
      have h3 : ∀ i : R, (∑ c : C, ∑ b : B, f i a b c * conj (f i a' b c)) = σ a a' := by
        intro i; simpa using hA i i a a'
      rw [Finset.sum_congr rfl (fun i _ => h3 i)]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [← Matrix.rank_self_mul_conjTranspose MA, hprod,
      rank_smul_ne_zero _ (by exact_mod_cast hRpos.ne') σ]
  have hMBrank : MB.rank = τ.rank := by
    have hprod : MB * MBᴴ = (Fintype.card R : ℂ) • τ := by
      ext b b'
      have h1 : (MB * MBᴴ) b b'
          = ∑ p : C × (R × A), f p.2.1 p.2.2 b p.1 * conj (f p.2.1 p.2.2 b' p.1) := by
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hMB]
      rw [h1, Fintype.sum_prod_type]
      have h2 : ∀ c : C, (∑ p : R × A, f p.1 p.2 b c * conj (f p.1 p.2 b' c))
          = ∑ i : R, ∑ a : A, f i a b c * conj (f i a b' c) := by
        intro c; rw [Fintype.sum_prod_type]
      simp only [h2]
      rw [Finset.sum_comm]
      have h3 : ∀ i : R, (∑ c : C, ∑ a : A, f i a b c * conj (f i a b' c)) = τ b b' := by
        intro i; simpa using hB i i b b'
      rw [Finset.sum_congr rfl (fun i _ => h3 i)]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [← Matrix.rank_self_mul_conjTranspose MB, hprod,
      rank_smul_ne_zero _ (by exact_mod_cast hRpos.ne') τ]
  -- the two merge inequalities
  have hmerge1 : Fintype.card R * σ.rank ≤ Fintype.card C * τ.rank := by
    have h1 : (MRAᵀ).rank ≤ Fintype.card C * MB.rank := by
      refine rank_merge_le _ _ ?_
      intro c b p
      rfl
    rw [Matrix.rank_transpose, hMRArank, hMBrank] at h1
    exact h1
  have hmerge2 : Fintype.card R * τ.rank ≤ Fintype.card C * σ.rank := by
    have h1 : (MRBᵀ).rank ≤ Fintype.card C * MA.rank := by
      refine rank_merge_le _ _ ?_
      intro c a p
      rfl
    rw [Matrix.rank_transpose, hMRBrank, hMArank] at h1
    exact h1
  -- positivity of the two ranks
  have hσ0 : σ a₀ a₀ ≠ 0 := by
    have h := hA i₀ i₀ a₀ a₀
    rw [if_pos rfl, one_mul] at h
    rw [← h]
    have hreal : (∑ c, ∑ b, f i₀ a₀ b c * conj (f i₀ a₀ b c))
        = ((∑ c, ∑ b, Complex.normSq (f i₀ a₀ b c) : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
        (Complex.mul_conj (f i₀ a₀ b c))
    rw [hreal]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    have hpos : 0 < (∑ c, ∑ b, Complex.normSq (f i₀ a₀ b c)) := by
      refine Finset.sum_pos' (fun c _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _)
        ⟨c₀, Finset.mem_univ _, ?_⟩
      refine Finset.sum_pos' (fun b _ => Complex.normSq_nonneg _) ⟨b₀, Finset.mem_univ _, ?_⟩
      exact Complex.normSq_pos.mpr hne
    exact hpos.ne'
  have hτ0 : τ b₀ b₀ ≠ 0 := by
    have h := hB i₀ i₀ b₀ b₀
    rw [if_pos rfl, one_mul] at h
    rw [← h]
    have hreal : (∑ c, ∑ a, f i₀ a b₀ c * conj (f i₀ a b₀ c))
        = ((∑ c, ∑ a, Complex.normSq (f i₀ a b₀ c) : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
        (Complex.mul_conj (f i₀ a b₀ c))
    rw [hreal]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    have hpos : 0 < (∑ c, ∑ a, Complex.normSq (f i₀ a b₀ c)) := by
      refine Finset.sum_pos' (fun c _ => Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _)
        ⟨c₀, Finset.mem_univ _, ?_⟩
      refine Finset.sum_pos' (fun a _ => Complex.normSq_nonneg _) ⟨a₀, Finset.mem_univ _, ?_⟩
      exact Complex.normSq_pos.mpr hne
    exact hpos.ne'
  have hσpos : 0 < σ.rank :=
    rank_pos_of_ne_zero σ (fun h => hσ0 (by rw [h]; rfl))
  have hτpos : 0 < τ.rank :=
    rank_pos_of_ne_zero τ (fun h => hτ0 (by rw [h]; rfl))
  -- conclude
  have hmul : (Fintype.card R * σ.rank) * (Fintype.card R * τ.rank)
      ≤ (Fintype.card C * τ.rank) * (Fintype.card C * σ.rank) :=
    Nat.mul_le_mul hmerge1 hmerge2
  have hsq : Fintype.card R * Fintype.card R ≤ Fintype.card C * Fintype.card C := by
    have hpos : 0 < σ.rank * τ.rank := Nat.mul_pos hσpos hτpos
    have : (Fintype.card R * Fintype.card R) * (σ.rank * τ.rank)
        ≤ (Fintype.card C * Fintype.card C) * (σ.rank * τ.rank) := by
      calc (Fintype.card R * Fintype.card R) * (σ.rank * τ.rank)
          = (Fintype.card R * σ.rank) * (Fintype.card R * τ.rank) := by ring
        _ ≤ (Fintype.card C * τ.rank) * (Fintype.card C * σ.rank) := hmul
        _ = (Fintype.card C * Fintype.card C) * (σ.rank * τ.rank) := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  nlinarith [hsq]

end CoreLemma

end QI

/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Core

/-!
# Quantum Singleton

The quantum Singleton bound (Knill–Laflamme bound): an `[[n, k, d]]_q` quantum code obeys
`n - k ≥ 2 (d - 1)`, stated here in the subtraction-free form `k + 2 * (d - 1) ≤ n`.
-/

open Matrix ComplexConjugate

namespace QI

variable {n q K : ℕ}

/-- Assemble a configuration of the `n` qudits out of its restrictions to `SA`, to `SB`,
and to the remaining qudits. -/
