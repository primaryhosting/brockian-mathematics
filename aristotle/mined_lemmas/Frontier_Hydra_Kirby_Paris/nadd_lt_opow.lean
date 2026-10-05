/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

theorem nadd_lt_opow {γ a b : Ordinal} (ha : a < ω ^ γ) (hb : b < ω ^ γ) : a ♯ b < ω ^ γ := by
  induction γ using Ordinal.induction generalizing a b with
  | _ γ IH =>
    rcases eq_or_ne a 0 with rfl | ha0
    · rwa [zero_nadd]
    rcases eq_or_ne b 0 with rfl | hb0
    · rwa [nadd_zero]
    have h1 : Ordinal.log ω a < γ := (Ordinal.lt_opow_iff_log_lt one_lt_omega0 ha0).1 ha
    have h2 : Ordinal.log ω b < γ := (Ordinal.lt_opow_iff_log_lt one_lt_omega0 hb0).1 hb
    set δ : Ordinal := max (Ordinal.log ω a) (Ordinal.log ω b) with hδ
    have hδγ : δ < γ := max_lt h1 h2
    have ha' : a < ω ^ (δ + 1) :=
      (Ordinal.lt_opow_iff_log_lt one_lt_omega0 ha0).2 (by
        simp [hδ])
    have hb' : b < ω ^ (δ + 1) :=
      (Ordinal.lt_opow_iff_log_lt one_lt_omega0 hb0).2 (by
        simp [hδ])
    have hIH : ∀ x y : Ordinal, x < ω ^ δ → y < ω ^ δ → x ♯ y < ω ^ δ :=
      fun x y hx hy => IH δ hδγ hx hy
    have := nadd_lt_opow_succ δ hIH a b ha' hb'
    exact this.trans_le (Ordinal.opow_le_opow_right omega0_pos (Order.add_one_le_iff.2 hδγ))

end Frontier

import Mathlib
import RequestProject.OrdinalNaddOpow

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Kirby–Paris hydra theorem

A *hydra* is a finite rooted tree, encoded as `Hydra.node : List Hydra → Hydra`.
Hercules chops off a *head* (a leaf) of the hydra; if the head was attached to the root
the hydra simply loses it, and otherwise the hydra grows `n` fresh copies of the subtree
hanging below the head's grandparent-child (i.e. below the head's parent, after the head
has been removed), attached to the head's grandparent.  The number `n` of copies is chosen
freely by the hydra at each round.

`Frontier.HydraStep n h h'` is the relation "`h'` is obtained from `h` by one round in which
the hydra grows `n` copies".  The theorem `Frontier.Hydra_Kirby_Paris` states that no infinite
battle exists: whatever heads Hercules chooses and whatever regrowth numbers the hydra chooses,
the game terminates.

The proof assigns to each hydra an ordinal below `ε₀`:
`ord (node [t₁,…,t_k]) = ω ^ ord t₁ ♯ ⋯ ♯ ω ^ ord t_k` (Hessenberg natural sum), and shows that
every round strictly decreases this ordinal.
-/

open Ordinal NaturalOps Order

namespace Frontier

/-- A hydra: a finite rooted tree, given by the list of subtrees hanging from its root. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/- The ordinal measure of a hydra, and of a list of hydras, defined by mutual recursion:
`ord (node l) = ordList l` and `ordList (t :: ts) = ω ^ ord t ♯ ordList ts`. -/
mutual

/-- The ordinal measure of a hydra: `ord (node [t₁,…,t_k]) = ω ^ ord t₁ ♯ ⋯ ♯ ω ^ ord t_k`. -/
