/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 does not allow a `/-! ... -/` module docstring to precede `import`, so the
-- required header comment is reproduced verbatim immediately after the import below.)

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

/-!
## Overview

We prove the **quantum Singleton bound** (Knill–Laflamme–Rains): an `[[n, k, d]]_q`
quantum error-correcting code satisfies `k + 2 * (d - 1) ≤ n`, i.e. `n - k ≥ 2 (d - 1)`.

The proof given here is a purely linear-algebraic ("Rényi-0"/rank) version of the usual
entropic no-cloning argument.  Writing the code space as a tensor `T` with a reference
index `R` (of size `q ^ k`) and three groups of sites `A`, `B`, `C`, the Knill–Laflamme
conditions for the two disjoint site sets `A` and `B` say that the Gram matrices of the
code vectors, partially traced onto `A` (resp. `B`), are proportional to the identity in
the reference index.  Passing to ranks:

* `rank ρ_{RA} = |R| · rank ρ_A` and `rank ρ_{RB} = |R| · rank ρ_B`  (Kronecker structure);
* `rank ρ_{BC} ≤ rank ρ_B · rank ρ_C`  (rank submultiplicativity across a tensor cut);
* `rank ρ_{RA} = rank ρ_{BC}` and `rank ρ_{RB} = rank ρ_{AC}` (purity).

Multiplying the two resulting inequalities `|R| · a ≤ b · c` and `|R| · b ≤ a · c` and
cancelling `a·b > 0` gives `|R| ≤ c ≤ q ^ |C|`, which is the bound.

No Mathlib lemma proves this statement (Mathlib contains no quantum coding theory), so the
required linear algebra — in particular a rank factorization of a matrix with one-sided
inverses, the rank of `1 ⊗ₖ S`, and submultiplicativity of the rank across a tensor cut —
is developed here from scratch.
-/

open Matrix Module Kronecker
open scoped ComplexOrder

namespace QI

/-! ### General linear algebra: rank tools -/

/-- **Rank factorization.**  Any matrix `N` factors as `N = F * G` where `F` has `rank N`
columns and a left inverse, and `G` has `rank N` rows and a right inverse. -/

theorem card_le_card_of_decoupled
    (T : R → A → B → C → ℂ) (SA : Matrix A A ℂ) (SB : Matrix B B ℂ)
    (hA : ∀ i j a a', ∑ b, ∑ c, T i a b c * conj (T j a' b c) = if i = j then SA a a' else 0)
    (hB : ∀ i j b b', ∑ a, ∑ c, T i a b c * conj (T j a b' c) = if i = j then SB b b' else 0)
    (i₀ : R) (hT : T i₀ ≠ 0) :
    Fintype.card R ≤ Fintype.card C := by
  classical
  set MA : Matrix (B × C) (R × A) ℂ := Matrix.of fun p d => T d.1 d.2 p.1 p.2 with hMA
  set MB : Matrix (A × C) (R × B) ℂ := Matrix.of fun p d => T d.1 p.1 d.2 p.2 with hMB
  set NB1 : Matrix B ((R × A) × C) ℂ := Matrix.of fun b p => T p.1.1 p.1.2 b p.2 with hNB1
  set NC1 : Matrix C ((R × A) × B) ℂ := Matrix.of fun c p => T p.1.1 p.1.2 p.2 c with hNC1
  set NA2 : Matrix A ((R × B) × C) ℂ := Matrix.of fun a p => T p.1.1 a p.1.2 p.2 with hNA2
  set NC2 : Matrix C ((R × B) × A) ℂ := Matrix.of fun c p => T p.1.1 p.2 p.1.2 c with hNC2
  -- lower bounds coming from the Kronecker structure of the Gram matrices
  have lowA : Fintype.card R * SA.rank ≤ MA.rank := by
    have h1 : MAᴴ * MA = (1 : Matrix R R ℂ) ⊗ₖ SAᵀ := by
      ext x y
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [Matrix.conjTranspose_apply, hMA, Matrix.of_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Matrix.transpose_apply, RCLike.star_def]
      rw [show (∑ b, ∑ c, conj (T x.1 x.2 b c) * T y.1 y.2 b c)
          = ∑ b, ∑ c, T y.1 y.2 b c * conj (T x.1 x.2 b c) from
        Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => mul_comm _ _))]
      rw [hA y.1 x.1 y.2 x.2]
      by_cases h : x.1 = y.1
      · simp [h]
      · simp [h, Ne.symm h]
    calc Fintype.card R * SA.rank = Fintype.card R * SAᵀ.rank := by rw [Matrix.rank_transpose]
      _ ≤ ((1 : Matrix R R ℂ) ⊗ₖ SAᵀ).rank := card_mul_rank_le_rank_one_kronecker _
      _ = (MAᴴ * MA).rank := by rw [h1]
      _ = MA.rank := Matrix.rank_conjTranspose_mul_self _
  have lowB : Fintype.card R * SB.rank ≤ MB.rank := by
    have h1 : MBᴴ * MB = (1 : Matrix R R ℂ) ⊗ₖ SBᵀ := by
      ext x y
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [Matrix.conjTranspose_apply, hMB, Matrix.of_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Matrix.transpose_apply, RCLike.star_def]
      rw [show (∑ a, ∑ c, conj (T x.1 a x.2 c) * T y.1 a y.2 c)
          = ∑ a, ∑ c, T y.1 a y.2 c * conj (T x.1 a x.2 c) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => mul_comm _ _))]
      rw [hB y.1 x.1 y.2 x.2]
      by_cases h : x.1 = y.1
      · simp [h]
      · simp [h, Ne.symm h]
    calc Fintype.card R * SB.rank = Fintype.card R * SBᵀ.rank := by rw [Matrix.rank_transpose]
      _ ≤ ((1 : Matrix R R ℂ) ⊗ₖ SBᵀ).rank := card_mul_rank_le_rank_one_kronecker _
      _ = (MBᴴ * MB).rank := by rw [h1]
      _ = MB.rank := Matrix.rank_conjTranspose_mul_self _
  -- upper bounds on the single-party ranks
  have upB : NB1.rank ≤ SB.rank := by
    have h1 : NB1 * NB1ᴴ = (Fintype.card R : ℂ) • SB := by
      ext b b'
      rw [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp only [Matrix.conjTranspose_apply, hNB1, Matrix.of_apply, RCLike.star_def,
        Matrix.smul_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hB i i b b')]
      simp [Finset.sum_const, mul_comm]
    calc NB1.rank = (NB1 * NB1ᴴ).rank := (Matrix.rank_self_mul_conjTranspose _).symm
      _ = ((Fintype.card R : ℂ) • SB).rank := by rw [h1]
      _ = (((Fintype.card R : ℂ) • (1 : Matrix B B ℂ)) * SB).rank := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ ≤ SB.rank := Matrix.rank_mul_le_right _ _
  have upA : NA2.rank ≤ SA.rank := by
    have h1 : NA2 * NA2ᴴ = (Fintype.card R : ℂ) • SA := by
      ext a a'
      rw [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp only [Matrix.conjTranspose_apply, hNA2, Matrix.of_apply, RCLike.star_def,
        Matrix.smul_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hA i i a a')]
      simp [Finset.sum_const, mul_comm]
    calc NA2.rank = (NA2 * NA2ᴴ).rank := (Matrix.rank_self_mul_conjTranspose _).symm
      _ = ((Fintype.card R : ℂ) • SA).rank := by rw [h1]
      _ = (((Fintype.card R : ℂ) • (1 : Matrix A A ℂ)) * SA).rank := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ ≤ SA.rank := Matrix.rank_mul_le_right _ _
  -- the two `C`-flattenings have the same rank
  have hCC : NC2.rank = NC1.rank := by
    let e : (R × B) × A ≃ (R × A) × B :=
      ⟨fun p => ((p.1.1, p.2), p.1.2), fun p => ((p.1.1, p.2), p.1.2),
        by rintro ⟨⟨i, b⟩, a⟩; rfl, by rintro ⟨⟨i, a⟩, b⟩; rfl⟩
    have h : NC2 = NC1.submatrix (Equiv.refl C) e := by ext c p; rfl
    rw [h, Matrix.rank_submatrix]
  -- submultiplicativity across the two cuts
  have subA : MA.rank ≤ NB1.rank * NC1.rank :=
    rank_le_mul_rank (fun (d : R × A) b c => T d.1 d.2 b c)
  have subB : MB.rank ≤ NA2.rank * NC2.rank :=
    rank_le_mul_rank (fun (d : R × B) a c => T d.1 a d.2 c)
  -- positivity
  obtain ⟨a₀, b₀, c₀, hne⟩ : ∃ a b c, T i₀ a b c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hT (funext fun a => funext fun b => funext fun c => h a b c)
  have hposA : 1 ≤ SA.rank := le_trans (rank_pos_of_ne_zero NA2 (by
    intro h
    exact hne (by simpa [hNA2] using congrFun (congrFun h a₀) ((i₀, b₀), c₀)))) upA
  have hposB : 1 ≤ SB.rank := le_trans (rank_pos_of_ne_zero NB1 (by
    intro h
    exact hne (by simpa [hNB1] using congrFun (congrFun h b₀) ((i₀, a₀), c₀)))) upB
  -- combine
  have e1 : Fintype.card R * SA.rank ≤ SB.rank * NC1.rank :=
    lowA.trans (subA.trans (Nat.mul_le_mul_right _ upB))
  have e2 : Fintype.card R * SB.rank ≤ SA.rank * NC1.rank := by
    refine lowB.trans (subB.trans ?_)
    rw [hCC]
    exact Nat.mul_le_mul_right _ upA
  have key : Fintype.card R * Fintype.card R * (SA.rank * SB.rank)
      ≤ (SA.rank * SB.rank) * (NC1.rank * NC1.rank) := by
    have := Nat.mul_le_mul e1 e2
    nlinarith [this]
  have hab : 0 < SA.rank * SB.rank := Nat.mul_pos hposA hposB
  have hsq : Fintype.card R * Fintype.card R ≤ NC1.rank * NC1.rank := by
    have h2 : (SA.rank * SB.rank) * (Fintype.card R * Fintype.card R)
        ≤ (SA.rank * SB.rank) * (NC1.rank * NC1.rank) := by linarith [key]
    exact Nat.le_of_mul_le_mul_left h2 hab
  exact (Nat.mul_self_le_mul_self_iff.mp hsq).trans (Matrix.rank_le_card_height _)

end Abstract


/-! ### Quantum error-correcting codes -/

/-- The computational-basis index set of `n` qudits of local dimension `q`. -/
abbrev Sites (n q : ℕ) : Type := Fin n → Fin q

/-- `embed A E` is the operator acting as `E` on the qudits located at the sites in `A`,
and as the identity on all the other sites. -/
