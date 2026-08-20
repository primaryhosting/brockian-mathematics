import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem induction {P : Circuit → Prop}
    (hvar : ∀ i, P (.var i)) (hconst : ∀ b, P (.const b))
    (hnot : ∀ c, P c → P c.cnot)
    (hor : ∀ cs, (∀ c ∈ cs, P c) → P (.cor cs))
    (hand : ∀ cs, (∀ c ∈ cs, P c) → P (.cand cs))
    (hmod : ∀ cs, (∀ c ∈ cs, P c) → P (.cmod cs)) : ∀ c, P c := by
  intro c
  induction c using Circuit.rec (motive_2 := fun cs => ∀ c ∈ cs, P c) with
  | var i => exact hvar i
  | const b => exact hconst b
  | cnot c ih => exact hnot c ih
  | cor cs ih => exact hor cs ih
  | cand cs ih => exact hand cs ih
  | cmod cs ih => exact hmod cs ih
  | nil => rename_i d hd; simp at hd
  | cons c cs ih ihs =>
      rename_i d hd
      rcases List.mem_cons.1 hd with h | h
      · subst h; exact ih
      · exact ihs d h

/-- The number of gates of a circuit. -/
