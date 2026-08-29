/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix Module ComplexConjugate
open scoped ComplexOrder

/-! ## Part I : linear algebra over `ℂ`

The mathematical core of the quantum Singleton bound is a statement about the ranks of the
various flattenings of a four-index complex tensor.  This part develops the required
rank inequalities.
-/

/-- Every column of a complex matrix can be expanded in a family of `X.rank` vectors, with
coefficients that are (fixed) linear functionals applied to the column. -/

theorem card_le_of_KL {R A B C : Type*} [Fintype R] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq R] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : R → A → B → C → ℂ) (σA : Matrix A A ℂ) (σB : Matrix B B ℂ)
    (hA : ∀ i j a a', (∑ b, ∑ c, T i a b c * conj (T j a' b c)) = if i = j then σA a a' else 0)
    (hB : ∀ i j b b', (∑ a, ∑ c, T i a b c * conj (T j a b' c)) = if i = j then σB b b' else 0)
    (hne : ∃ i a b c, T i a b c ≠ 0) :
    Fintype.card R ≤ Fintype.card C := by
  classical
  set K := Fintype.card R with hK
  set MA : Matrix (R × A) (B × C) ℂ := Matrix.of fun p q => T p.1 p.2 q.1 q.2 with hMA
  set MB : Matrix (R × B) (A × C) ℂ := Matrix.of fun p q => T p.1 q.1 p.2 q.2 with hMB
  set FA : Matrix A (R × B × C) ℂ := Matrix.of fun a p => T p.1 a p.2.1 p.2.2 with hFA
  set FB : Matrix B (R × A × C) ℂ := Matrix.of fun b p => T p.1 p.2.1 b p.2.2 with hFB
  set FC : Matrix C (R × A × B) ℂ := Matrix.of fun c p => T p.1 p.2.1 p.2.2 c with hFC
  -- Step 1 : correctability of `A` forces `rank MA ≥ K * rank σA`.
  have h1 : K * σA.rank ≤ MA.rank := by
    have hprod : MA * MAᴴ
        = Matrix.of (fun (p q : R × A) => if p.1 = q.1 then σA p.2 q.2 else 0) := by
      funext p q
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hMA, Matrix.of_apply,
        Fintype.sum_prod_type, RCLike.star_def]
      exact hA p.1 q.1 p.2 q.2
    calc K * σA.rank
        ≤ (Matrix.of (fun (p q : R × A) => if p.1 = q.1 then σA p.2 q.2 else 0)).rank :=
          rank_blockdiag_ge σA
      _ = (MA * MAᴴ).rank := by rw [hprod]
      _ = MA.rank := Matrix.rank_self_mul_conjTranspose MA
  have h1' : K * σB.rank ≤ MB.rank := by
    have hprod : MB * MBᴴ
        = Matrix.of (fun (p q : R × B) => if p.1 = q.1 then σB p.2 q.2 else 0) := by
      funext p q
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hMB, Matrix.of_apply,
        Fintype.sum_prod_type, RCLike.star_def]
      exact hB p.1 q.1 p.2 q.2
    calc K * σB.rank
        ≤ (Matrix.of (fun (p q : R × B) => if p.1 = q.1 then σB p.2 q.2 else 0)).rank :=
          rank_blockdiag_ge σB
      _ = (MB * MBᴴ).rank := by rw [hprod]
      _ = MB.rank := Matrix.rank_self_mul_conjTranspose MB
  -- Step 2 : the two flattening bounds.
  have h2 : MA.rank ≤ FB.rank * FC.rank := rank_tensor_le T
  have h2' : MB.rank ≤ FA.rank * FC.rank := by
    have hmain := rank_tensor_le (fun (i : R) (b : B) (a : A) (c : C) => T i a b c)
    have e1 : (Matrix.of fun (a : A) (p : R × B × C) => T p.1 a p.2.1 p.2.2) = FA := rfl
    have e2 : (Matrix.of fun (c : C) (p : R × B × A) => T p.1 p.2.2 p.2.1 c)
        = FC.submatrix id (fun p => (p.1, p.2.2, p.2.1)) := rfl
    rw [e1, e2] at hmain
    have e3 : (FC.submatrix id (fun p : R × B × A => (p.1, p.2.2, p.2.1))).rank = FC.rank :=
      Matrix.rank_submatrix FC (Equiv.refl C) ((Equiv.refl R).prodCongr (Equiv.prodComm B A))
    rw [e3] at hmain
    exact hmain
  -- Step 3 : `rank FA ≤ rank σA` and `rank FB ≤ rank σB`.
  have h3 : FA.rank ≤ σA.rank := by
    have hprod : FA * FAᴴ = (K : ℂ) • σA := by
      funext a a'
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hFA, Matrix.of_apply,
        Fintype.sum_prod_type, RCLike.star_def, Matrix.smul_apply, smul_eq_mul]
      rw [show (∑ i : R, ∑ b : B, ∑ c : C, T i a b c * conj (T i a' b c))
            = ∑ _i : R, σA a a' from Finset.sum_congr rfl (fun i _ => by
              simpa using hA i i a a')]
      simp [hK, mul_comm]
    calc FA.rank = (FA * FAᴴ).rank := (Matrix.rank_self_mul_conjTranspose FA).symm
      _ = ((K : ℂ) • σA).rank := by rw [hprod]
      _ ≤ σA.rank := rank_smul_le _ _
  have h4 : FB.rank ≤ σB.rank := by
    have hprod : FB * FBᴴ = (K : ℂ) • σB := by
      funext b b'
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hFB, Matrix.of_apply,
        Fintype.sum_prod_type, RCLike.star_def, Matrix.smul_apply, smul_eq_mul]
      rw [show (∑ i : R, ∑ a : A, ∑ c : C, T i a b c * conj (T i a b' c))
            = ∑ _i : R, σB b b' from Finset.sum_congr rfl (fun i _ => by
              simpa using hB i i b b')]
      simp [hK, mul_comm]
    calc FB.rank = (FB * FBᴴ).rank := (Matrix.rank_self_mul_conjTranspose FB).symm
      _ = ((K : ℂ) • σB).rank := by rw [hprod]
      _ ≤ σB.rank := rank_smul_le _ _
  -- Step 4 : the reduced correlations are nonzero.
  obtain ⟨i0, a0, b0, c0, hne0⟩ := hne
  have hσA : 1 ≤ σA.rank := by
    refine rank_pos_of_ne_zero σA ?_
    intro h0
    refine double_sum_mul_conj_ne_zero (fun b c => T i0 a0 b c) b0 c0 hne0 ?_
    rw [hA i0 i0 a0 a0, h0]
    simp
  have hσB : 1 ≤ σB.rank := by
    refine rank_pos_of_ne_zero σB ?_
    intro h0
    refine double_sum_mul_conj_ne_zero (fun a c => T i0 a b0 c) a0 c0 hne0 ?_
    rw [hB i0 i0 b0 b0, h0]
    simp
  -- Step 5 : arithmetic.
  have hC : FC.rank ≤ Fintype.card C := Matrix.rank_le_card_height FC
  have i1 : K * σA.rank ≤ σB.rank * FC.rank :=
    le_trans (le_trans h1 h2) (Nat.mul_le_mul_right _ h4)
  have i2 : K * σB.rank ≤ σA.rank * FC.rank :=
    le_trans (le_trans h1' h2') (Nat.mul_le_mul_right _ h3)
  have key : K * K * (σA.rank * σB.rank) ≤ (FC.rank * FC.rank) * (σA.rank * σB.rank) := by
    calc K * K * (σA.rank * σB.rank) = (K * σA.rank) * (K * σB.rank) := by ring
      _ ≤ (σB.rank * FC.rank) * (σA.rank * FC.rank) := Nat.mul_le_mul i1 i2
      _ = (FC.rank * FC.rank) * (σA.rank * σB.rank) := by ring
  have hKK : K * K ≤ FC.rank * FC.rank :=
    Nat.le_of_mul_le_mul_right key (Nat.mul_pos hσA hσB)
  have hfin : K ≤ FC.rank := by nlinarith [hKK]
  exact le_trans hfin hC

/-! ## Part II : quantum codes

The Hilbert space of `n` qudits of local dimension `q` is `ℂ^(Fin n → Fin q)`, i.e. the space
of functions on the set `Str n q` of computational basis labels ("strings").
-/

/-- Computational basis labels ("strings") for `n` qudits of local dimension `q`. -/
abbrev Str (n q : ℕ) := Fin n → Fin q

/-- The Hilbert space of `n` qudits of local dimension `q`. -/
abbrev HSpace (n q : ℕ) := EuclideanSpace ℂ (Str n q)

/-- `glue S u w` is the string taking its coordinates on the sites `S` from `u`, and its
remaining coordinates from `w`. -/
