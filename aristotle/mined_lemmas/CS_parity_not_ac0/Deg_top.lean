import Mathlib

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators

namespace CS

/-- The field with three elements. -/
abbrev F3 := ZMod 3

/-- The Boolean cube on `n` coordinates. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- `±1` encoding of a Boolean value inside `F3`. -/

lemma Deg_top (n : ℕ) : Deg n n = ⊤ := by
  rw [eq_top_iff]
  intro f _
  -- write `f` as a combination of point indicators
  have hdelta : ∀ z : Cube n, (fun x => (2 : F3)^n * ∏ i : Fin n, (1 + sgn (z i) * sgn (x i)))
      ∈ Deg n n := by
    intro z
    have hexp : (fun x : Cube n => ∏ i : Fin n, (1 + sgn (z i) * sgn (x i)))
        = ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset,
            (∏ i ∈ Finset.univ \ A, sgn (z i)) • mono (Finset.univ \ A) := by
      funext x
      rw [Finset.prod_add, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro A _
      simp only [mono, Pi.smul_apply, smul_eq_mul, Finset.prod_const_one, one_mul]
      rw [← Finset.prod_mul_distrib]
    have h1 : (fun x : Cube n => ∏ i : Fin n, (1 + sgn (z i) * sgn (x i))) ∈ Deg n n := by
      rw [hexp]
      refine Submodule.sum_mem _ ?_
      intro A _
      exact Submodule.smul_mem _ _ (mono_mem_Deg (by
        simpa using Finset.card_le_univ (Finset.univ \ A)))
    have h2 : (fun x : Cube n => (2 : F3)^n * ∏ i : Fin n, (1 + sgn (z i) * sgn (x i)))
        = ((2 : F3)^n) • (fun x : Cube n => ∏ i : Fin n, (1 + sgn (z i) * sgn (x i))) := by
      funext x; simp
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  have key : f = ∑ z : Cube n, f z • (fun x => (2 : F3)^n * ∏ i : Fin n,
      (1 + sgn (z i) * sgn (x i))) := by
    funext x
    rw [Finset.sum_apply]
    have hz : ∀ z : Cube n, ((2 : F3)^n * ∏ i : Fin n, (1 + sgn (z i) * sgn (x i)))
        = if z = x then 1 else 0 := by
      intro z
      by_cases h : z = x
      · subst h
        have : ∀ i : Fin n, (1 : F3) + sgn (z i) * sgn (z i) = 2 := by
          intro i; rw [sgn_mul_self]; ring
        simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, if_pos]
        rw [← mul_pow]
        have h22 : (2 : F3) * 2 = 1 := by decide
        rw [h22, one_pow]
        simp
      · have : ∃ i, z i ≠ x i := by
          by_contra hc
          push_neg at hc
          exact h (funext hc)
        obtain ⟨i, hi⟩ := this
        have hzero : (1 : F3) + sgn (z i) * sgn (x i) = 0 := by
          cases hz' : z i <;> cases hx' : x i <;> simp [hz', hx'] at hi ⊢ <;> simp [sgn] <;> decide
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
        simp [h]
    simp only [Pi.smul_apply, smul_eq_mul, hz]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [key]
  exact Submodule.sum_mem _ (fun z _ => Submodule.smul_mem _ _ (hdelta z))

end CS

import Mathlib

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
set_option pp.piBinderTypes true

set_option grind.warning false

