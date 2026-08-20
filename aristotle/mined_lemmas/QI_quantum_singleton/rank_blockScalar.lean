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

open Matrix ComplexConjugate
open scoped BigOperators ComplexOrder

namespace QI

/-! ## Linear-algebra preliminaries -/

section RankLemmas

variable {X Y : Type*}

/-- Rank–nullity for the linear map `v ↦ M *ᵥ v`. -/

lemma rank_blockScalar {R A : Type*} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
    (σ : Matrix A A ℂ) :
    (Matrix.of fun p p' : R × A => (if p.1 = p'.1 then (1 : ℂ) else 0) * σ p.2 p'.2).rank
      = Fintype.card R * σ.rank := by
  classical
  set P : Matrix (R × A) (R × A) ℂ :=
    Matrix.of fun p p' : R × A => (if p.1 = p'.1 then (1 : ℂ) else 0) * σ p.2 p'.2 with hP
  have key : ∀ (v : R × A → ℂ) (r : R) (a : A),
      (P *ᵥ v) (r, a) = (σ *ᵥ (fun a' => v (r, a'))) a := by
    intro v r a
    simp only [Matrix.mulVec, dotProduct, hP, Matrix.of_apply]
    rw [Fintype.sum_prod_type]
    simp
  -- the kernel of `P` is `R` copies of the kernel of `σ`
  have hker : Module.finrank ℂ (LinearMap.ker P.mulVecLin)
      = Fintype.card R * Module.finrank ℂ (LinearMap.ker σ.mulVecLin) := by
    have hmem : ∀ f : R → (LinearMap.ker σ.mulVecLin),
        P.mulVecLin (fun p => (f p.1).1 p.2) = 0 := by
      intro f
      funext p
      obtain ⟨r, a⟩ := p
      have hk : (P *ᵥ (fun p : R × A => (f p.1).1 p.2)) (r, a) = (σ *ᵥ (f r).1) a := key _ r a
      have h1 : σ *ᵥ (f r).1 = 0 := by
        have h2 := (f r).2
        rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
      simp only [Matrix.mulVecLin_apply, hk, h1]
      rfl
    let Φ : (R → (LinearMap.ker σ.mulVecLin)) →ₗ[ℂ] (LinearMap.ker P.mulVecLin) :=
    { toFun := fun f => ⟨fun p => (f p.1).1 p.2, by rw [LinearMap.mem_ker]; exact hmem f⟩
      map_add' := by intros f g; ext p; simp
      map_smul' := by intros c f; ext p; simp }
    have hbij : Function.Bijective Φ := by
      constructor
      · intro f g hfg
        funext r
        apply Subtype.ext
        funext a
        exact congrFun (congrArg Subtype.val hfg) (r, a)
      · rintro ⟨v, hv⟩
        rw [LinearMap.mem_ker] at hv
        refine ⟨fun r => ⟨fun a => v (r, a), ?_⟩, ?_⟩
        · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
          funext a
          have hk : (P *ᵥ v) (r, a) = (σ *ᵥ (fun a' => v (r, a'))) a := key v r a
          have h0 : (P *ᵥ v) (r, a) = 0 := by
            have := congrFun hv (r, a); rwa [Matrix.mulVecLin_apply] at this
          rw [← hk, h0]; rfl
        · apply Subtype.ext; funext p; rfl
    have hfr := (LinearEquiv.ofBijective Φ hbij).finrank_eq
    rw [← hfr, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h1 := rank_add_finrank_ker P
  have h2 := rank_add_finrank_ker σ
  rw [hker, Fintype.card_prod] at h1
  have h3 : P.rank + Fintype.card R * Module.finrank ℂ (LinearMap.ker σ.mulVecLin)
      = Fintype.card R * σ.rank
        + Fintype.card R * Module.finrank ℂ (LinearMap.ker σ.mulVecLin) := by
    rw [h1, ← Nat.mul_add, h2]
  exact Nat.add_right_cancel h3

/-- For a positive semidefinite bipartite matrix `ρ`, a vector killed by the partial trace
`ρX`, tensored with a basis vector of `Y`, is killed by `ρ`. -/
