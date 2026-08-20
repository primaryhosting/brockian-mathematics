import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem gate_dichotomy (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) [Fact q.Prime]
    [CharP F q] (x : Fin n → Bool) (i : Fin C.size) :
    (∀ ρ : Rand C t, LocalGood F C q t ρ x i) ∨
    ∃ (S : Finset (Fin i.val)) (w : Fin i.val → Bool) (j₀ : Fin i.val),
      j₀ ∈ S ∧ w j₀ = true ∧
      ∀ ρ : Rand C t, ¬ LocalGood F C q t ρ x i →
        ∀ κ : Fin t, q ∣ (S.filter (fun j => ρ i κ (C.up i j) = true ∧ w j = true)).card := by
  rcases hg : C.gate i with j | b | j | S | S | L
  · left; intro ρ _
    simp only [Good, gpoly_inp F C q t ρ i j hg, gval_inp C q x i j hg]
    simp [mono_apply, ind]
  · left; intro ρ _
    simp only [Good, gpoly_cst F C q t ρ i b hg, gval_cst C q x i b hg]
  · left; intro ρ hch
    simp only [Good, gpoly_notg F C q t ρ i j hg, gval_notg C q x i j hg]
    simp only [Pi.sub_apply, Pi.one_apply]
    rw [show gpoly F C q t ρ (C.up i j) x = ind F (C.gval q x (C.up i j)) from hch j, ← ind_not]
  · exact gate_dichotomy_org F C q t x i S hg
  · exact gate_dichotomy_andg F C q t x i S hg
  · left; intro ρ hch
    simp only [Good, gpoly_modg F C q t ρ i L hg, gval_modg C q x i L hg]
    simp only [Pi.pow_apply]
    rw [list_sum_apply, List.map_map]
    have hmap : ((fun f => f x) ∘ fun j => gpoly F C q t ρ (C.up i j))
        = fun j => ind F (C.gval q x (C.up i j)) := by
      funext j; exact hch j
    rw [hmap, list_sum_ind, natCast_pow_card_sub_one q]
    by_cases hd : q ∣ (List.filter (fun j => C.gval q x (C.up i j)) L).length
    · rw [if_pos hd]; simp [ind, hd]
    · rw [if_neg hd]; simp [ind, hd]

/-- For every gate and every input, the fraction of random choices for which the gate fails
is at most `2^{-t}`. -/
