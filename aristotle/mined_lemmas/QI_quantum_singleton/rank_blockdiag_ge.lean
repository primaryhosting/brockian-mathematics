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

theorem rank_blockdiag_ge {R A : Type*} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
    (σ : Matrix A A ℂ) :
    Fintype.card R * σ.rank ≤
      (Matrix.of (fun (p q : R × A) => if p.1 = q.1 then σ p.2 q.2 else 0)).rank := by
  classical
  set D : Matrix (R × A) (R × A) ℂ :=
    Matrix.of (fun p q => if p.1 = q.1 then σ p.2 q.2 else 0) with hD
  set W := LinearMap.range σ.mulVecLin with hW
  have hfrW : finrank ℂ W = σ.rank := rfl
  let bs : Basis (Fin σ.rank) ℂ W := (Module.finBasis ℂ W).reindex (finCongr hfrW)
  set w : R × Fin σ.rank → (R × A → ℂ) :=
    fun x z => if z.1 = x.1 then ((bs x.2 : W) : A → ℂ) z.2 else 0 with hw
  have hmem : ∀ x, w x ∈ LinearMap.range D.mulVecLin := by
    rintro ⟨i, p⟩
    obtain ⟨y, hy⟩ := (bs p).2
    refine ⟨fun z => if z.1 = i then y z.2 else 0, ?_⟩
    funext z
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hD, Matrix.of_apply, hw]
    by_cases h : z.1 = i
    · simp only [h]
      rw [← hy]
      simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, apply_ite]
    · simp only [h, if_false]
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : x.1 = i <;> simp [hx, h]
  have hli : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc x
    have hval : ∀ (j : R) (a : A), ∑ p : Fin σ.rank, c (j, p) * ((bs p : W) : A → ℂ) a = 0 := by
      intro j a
      have := congrFun hc (j, a)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hw, Pi.zero_apply,
        Fintype.sum_prod_type] at this
      simpa using this
    have hbsli : LinearIndependent ℂ (fun p : Fin σ.rank => ((bs p : W) : A → ℂ)) :=
      (bs.linearIndependent).map' W.subtype (by simp)
    rw [Fintype.linearIndependent_iff] at hbsli
    exact hbsli (fun p => c (x.1, p)) (by funext a; simpa using hval x.1 a) x.2
  have hli' := hli.of_comp (Submodule.subtype (LinearMap.range D.mulVecLin))
    (v := fun x => (⟨w x, hmem x⟩ : LinearMap.range D.mulVecLin))
  simpa [Matrix.rank, Fintype.card_prod] using hli'.fintype_card_le_finrank

/-- The `(R×A) | (B×C)` flattening of a tensor has rank at most the product of the ranks of its
`B` and `C` flattenings. -/
