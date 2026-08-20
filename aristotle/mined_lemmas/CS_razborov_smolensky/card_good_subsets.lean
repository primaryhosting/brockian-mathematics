import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem card_good_subsets (q m : ℕ) (hq : 2 ≤ q) (z : Fin m → Bool) (i₀ : Fin m)
    (hz : z i₀ = true) :
    2 * #(univ.filter (fun S : Finset (Fin m) =>
      (#(S.filter (fun i => z i = true))) % q = 0)) ≤ 2 ^ m := by
  classical
  set c : Finset (Fin m) → ℕ := fun S => #(S.filter (fun i => z i = true)) with hc
  set G := univ.filter (fun S : Finset (Fin m) => c S % q = 0) with hG
  set f : Finset (Fin m) → Finset (Fin m) := fun S => if i₀ ∈ S then S.erase i₀ else insert i₀ S
    with hf
  have hstep : ∀ S, (i₀ ∈ S → c (f S) + 1 = c S) ∧ (i₀ ∉ S → c (f S) = c S + 1) := by
    intro S
    constructor
    · intro h
      simp only [hf, if_pos h, hc]
      rw [Finset.filter_erase, Finset.card_erase_of_mem (by simp [h, hz])]
      have : 1 ≤ #(S.filter (fun i => z i = true)) :=
        Finset.card_pos.2 ⟨i₀, by simp [h, hz]⟩
      omega
    · intro h
      simp only [hf, if_neg h, hc]
      rw [Finset.filter_insert, if_pos hz, Finset.card_insert_of_notMem (by simp [h])]
  have hinv : ∀ S, f (f S) = S := by
    intro S
    by_cases h : i₀ ∈ S
    · simp only [hf, if_pos h]
      rw [if_neg (by simp)]
      exact Finset.insert_erase h
    · simp only [hf, if_neg h]
      rw [if_pos (by simp)]
      exact Finset.erase_insert h
  have hinj : Function.Injective f := Function.LeftInverse.injective hinv
  have hmaps : ∀ S ∈ G, f S ∈ univ \ G := by
    intro S hS
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hG, Finset.mem_filter]
    intro hbad
    have hd1 : q ∣ c S := Nat.dvd_of_mod_eq_zero hS
    have hd2 : q ∣ c (f S) := Nat.dvd_of_mod_eq_zero hbad
    have hone : q ∣ 1 := by
      by_cases h : i₀ ∈ S
      · have he := (hstep S).1 h
        exact (Nat.dvd_add_iff_right hd2).mpr (by rwa [he])
      · have he := (hstep S).2 h
        exact (Nat.dvd_add_iff_right hd1).mpr (by rwa [he] at hd2)
    have := Nat.le_of_dvd one_pos hone
    omega
  have hcard : #G ≤ #(univ \ G) := Finset.card_le_card_of_injOn f hmaps hinj.injOn
  have htot : #(univ : Finset (Finset (Fin m))) = 2 ^ m := by
    simp [Finset.card_univ, Fintype.card_finset]
  have hsd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ G)
  omega

end CS

import Mathlib

/-!
# Constant-depth circuits with `MOD q` gates

This file sets up the syntax and semantics of unbounded fan-in Boolean circuits with
`AND`, `OR`, `NOT` and `MOD q` gates, the `MOD p` Boolean function, and the class `AC⁰[q]`.

Circuits are represented as *trees*.  This is no loss of generality for the class `AC⁰[q]`:
unfolding a depth-`d`, size-`S` DAG circuit into a tree yields a tree of size at most `S ^ d`,
which is still polynomial when `d` is a constant.  Thus the class of functions defined below
is exactly `AC⁰[q]`.
-/

namespace CS

/-- Boolean circuits with unbounded fan-in `AND`, `OR` and `MOD` gates, and `NOT` gates.
Input variables are indexed by natural numbers. -/
inductive Circuit : Type where
  | var : ℕ → Circuit
  | const : Bool → Circuit
  | cnot : Circuit → Circuit
  | cor : List Circuit → Circuit
  | cand : List Circuit → Circuit
  | cmod : List Circuit → Circuit

namespace Circuit

/-- Induction principle for circuits. -/
@[elab_as_elim]
