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

import Mathlib
import RequestProject.RS.Degree

/-!
# Probabilistic polynomial approximation of `AC⁰[q]` circuits

The Razborov–Smolensky approximation lemma: a circuit of size `s` and depth `d` over
`{¬, ∧, ∨, MOD q}` can be approximated over a field of characteristic `q` by a function of
degree `(ℓ (q-1))^d` which errs on at most `s · 2^(n-ℓ)` inputs.
-/

set_option maxHeartbeats 1000000

namespace CS

open Finset

variable {F : Type*} [Field F] {n q : ℕ}

/-- The set of inputs on which `g` differs from the Boolean function `h`. -/

lemma card_bad_omega_le {k ℓ : ℕ} (hq : q.Prime) [CharP F q] (u : Fin k → Cube n → F)
    (b : Fin k → Cube n → Bool) (x : Cube n) (hx : ∀ i, u i x = boolF F (b i x))
    (W : Finset (Fin ℓ → Fin k → Bool))
    (hW : ∀ ω ∈ W, orPoly q ω u x ≠ boolF F (decide (∃ i, b i x = true))) :
    W.card * 2 ^ ℓ ≤ 2 ^ (k * ℓ) := by
  classical
  by_cases hT : ∃ i, b i x = true
  · obtain ⟨i₀, hi₀⟩ := hT
    set BadS : Finset (Fin k → Bool) := {S : Fin k → Bool | q ∣ cnt fun i => S i && b i x}
      with hBadS
    have hsub : W ⊆ Fintype.piFinset (fun _ : Fin ℓ => BadS) := by
      intro ω hω
      simp only [Fintype.mem_piFinset, hBadS, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hc
      push_neg at hc
      obtain ⟨j, hj⟩ := hc
      apply hW ω hω
      have hprod : ∏ j' : Fin ℓ, (1 - (∑ i, if ω j' i then u i x else 0) ^ (q - 1)) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
        rw [sel_sum_eq u b x hx (ω j), natCast_pow_sub_one hq, if_neg hj]
        ring
      simp only [orPoly, hprod, sub_zero]
      rw [decide_eq_true (⟨i₀, hi₀⟩ : ∃ i, b i x = true)]
      simp [boolF]
    refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card hsub)) ?_
    rw [Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc BadS.card ^ ℓ * 2 ^ ℓ = (2 * BadS.card) ^ ℓ := by rw [mul_pow]; ring
      _ ≤ (2 ^ k) ^ ℓ := Nat.pow_le_pow_left (card_bad_subsets_le hq.two_le _ i₀ hi₀) ℓ
      _ = 2 ^ (k * ℓ) := by rw [← pow_mul]
  · push_neg at hT
    have hWe : W = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun ω hω => ?_
      refine hW ω hω ?_
      have hz : ∀ j : Fin ℓ, (∑ i, if ω j i then u i x else 0) = 0 := by
        intro j
        rw [sel_sum_eq u b x hx (ω j)]
        have hc0 : (cnt fun i => ω j i && b i x) = 0 := by
          simp only [cnt, Finset.card_eq_zero]
          refine Finset.filter_eq_empty_iff.2 fun i _ => ?_
          simp [hT i]
        rw [hc0]
        simp
      have hprod : ∏ j : Fin ℓ, (1 - (∑ i, if ω j i then u i x else 0) ^ (q - 1)) = 1 := by
        refine Finset.prod_eq_one fun j _ => ?_
        rw [hz j, zero_pow (by have := hq.two_le; omega), sub_zero]
      simp only [orPoly, hprod, sub_self]
      have hnex : ¬ ∃ i, b i x = true := by push_neg; exact hT
      rw [decide_eq_false hnex]
      simp [boolF]
    rw [hWe]
    simp

/-- Existence of a good choice of random subsets for an `OR` gate. -/
