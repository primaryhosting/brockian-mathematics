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

theorem rank_tensor_le {R A B C : Type*} [Fintype R] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] [DecidableEq R] [DecidableEq A]
    (T : R → A → B → C → ℂ) :
    (Matrix.of fun (p : R × A) (q : B × C) => T p.1 p.2 q.1 q.2).rank ≤
      (Matrix.of fun (b : B) (p : R × A × C) => T p.1 p.2.1 b p.2.2).rank *
      (Matrix.of fun (c : C) (p : R × A × B) => T p.1 p.2.1 p.2.2 c).rank := by
  classical
  set FB : Matrix B (R × A × C) ℂ := Matrix.of fun b p => T p.1 p.2.1 b p.2.2 with hFB
  set FC : Matrix C (R × A × B) ℂ := Matrix.of fun c p => T p.1 p.2.1 p.2.2 c with hFC
  obtain ⟨e, cf, he⟩ := exists_col_expansion FB
  set Z : Matrix C (Fin FB.rank × R × A) ℂ :=
    Matrix.of fun c x => ∑ β, cf x.1 β * T x.2.1 x.2.2 β c with hZ
  have hZrank : Z.rank ≤ FC.rank := by
    have hfac : Z = FC * (Matrix.of fun (y : R × A × B) (x : Fin FB.rank × R × A) =>
        if x.2 = (y.1, y.2.1) then cf x.1 y.2.2 else 0) := by
      funext c x
      simp only [hZ, hFC, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
      simp only [mul_ite, mul_zero]
      simp [Prod.ext_iff, eq_comm, ite_and, Finset.sum_ite_eq', mul_comm]
    rw [hfac]
    exact Matrix.rank_mul_le_left _ _
  obtain ⟨g, dg, hg⟩ := exists_col_expansion Z
  have key : ∀ i a b c, T i a b c
      = ∑ p : Fin FB.rank, ∑ s : Fin Z.rank,
          (e p b * g s c) * (∑ γ, dg s γ * Z γ (p, i, a)) := by
    intro i a b c
    have h1 : T i a b c = ∑ p, e p b * (∑ β, cf p β * T i a β c) := he b (i, a, c)
    have h2 : ∀ p, (∑ β, cf p β * T i a β c) = Z c (p, i, a) := by intro p; simp [hZ]
    have h3 : ∀ p, Z c (p, i, a) = ∑ s, g s c * (∑ γ, dg s γ * Z γ (p, i, a)) :=
      fun p => hg c (p, i, a)
    rw [h1]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [h2 p, h3 p, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hfac : (Matrix.of fun (p : R × A) (q : B × C) => T p.1 p.2 q.1 q.2)
      = (Matrix.of fun (p : R × A) (x : Fin FB.rank × Fin Z.rank) =>
            ∑ γ, dg x.2 γ * Z γ (x.1, p.1, p.2))
        * (Matrix.of fun (x : Fin FB.rank × Fin Z.rank) (q : B × C) => e x.1 q.1 * g x.2 q.2) := by
    funext p q
    simp only [Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type]
    rw [key p.1 p.2 q.1 q.2]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring
  rw [hfac]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  refine le_trans (Matrix.rank_le_card_width _) ?_
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_le_mul_left _ hZrank

/-- A nonzero matrix has positive rank. -/
