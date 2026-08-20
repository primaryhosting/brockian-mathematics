/-
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalize the Kirby–Paris hydra game and prove that **every** play terminates,
no matter which head Hercules chops and no matter how many copies the hydra grows
at each stage (so, in particular, for every strategy).

A hydra is a finite rooted tree, encoded as `Hydra.node : List Hydra → Hydra`.
A *head* is a leaf.  In one move Hercules chops off a head; if the head has a
grandparent, the grandparent grows `n` extra copies of the subtree hanging at the
head's parent (with the head already removed).  The number `n` may be arbitrary
and may change from move to move.

The proof is the classical one: we attach to a hydra the ordinal
`o(node [h₁,…,h_k]) = ω ^ o(h₁) ♯ ⋯ ♯ ω ^ o(h_k) < ε₀`
(`♯` is the natural / Hessenberg sum) and check that every move strictly decreases
it; well-foundedness of the ordinals then finishes the argument.

The ordinal-arithmetic input that is not in Mathlib is that `ω ^ d` is closed under
natural sums; this is proved from scratch in the first section
(`Frontier.nadd_lt_opow_omega0`).

By the Kirby–Paris theorem this termination statement is not provable in Peano
arithmetic; the proof below is of course carried out in the ambient set theory of
Lean/Mathlib, where transfinite induction below ε₀ is available.
-/

open Ordinal NaturalOps

namespace Frontier

/-! ## Part 1: `ω ^ d` is closed under natural addition -/

/-- The key estimate: natural addition of two ordinals below `W * ω` is bounded by
the "Cantor-like" expression built from their quotients and remainders modulo `W`,
provided `W` itself is closed under natural addition. -/

theorem nadd_bound (W : Ordinal) (hW : W ≠ 0)
    (hCl : ∀ x y : Ordinal, x < W → y < W → x ♯ y < W) :
    ∀ a b : Ordinal, a < W * ω → b < W * ω →
      a ♯ b ≤ W * (a / W + b / W) + (a % W ♯ b % W) := by
  intro a
  induction a using Ordinal.induction with
  | h a IHa =>
  intro b
  induction b using Ordinal.induction with
  | h b IHb =>
  intro ha hb
  have hqa : a / W < ω := (Ordinal.div_lt hW).2 ha
  have hqb : b / W < ω := (Ordinal.div_lt hW).2 hb
  obtain ⟨na, hna⟩ := Ordinal.lt_omega0.1 hqa
  obtain ⟨nb, hnb⟩ := Ordinal.lt_omega0.1 hqb
  rw [Ordinal.nadd_le_iff]
  constructor
  · intro a' ha'
    have h1 := IHa a' ha' b (ha'.trans ha) hb
    have hq : a' / W ≤ a / W := Ordinal.div_le_left ha'.le _
    rcases lt_or_eq_of_le hq with hlt | heq
    · refine h1.trans_lt ?_
      have hr : a' % W ♯ b % W < W := hCl _ _ (Ordinal.mod_lt _ hW) (Ordinal.mod_lt _ hW)
      obtain ⟨na', hna'⟩ := Ordinal.lt_omega0.1 (hlt.trans hqa)
      have hlt' : na' < na := by rw [hna', hna] at hlt; exact_mod_cast hlt
      calc W * (a' / W + b / W) + (a' % W ♯ b % W)
          < W * (a' / W + b / W) + W := add_lt_add_right hr _
        _ = W * (a' / W + b / W + 1) := by rw [mul_add_one]
        _ ≤ W * (a / W + b / W) := by
            refine mul_le_mul_right ?_ W
            rw [hna, hnb, hna']
            have : (na' + nb + 1 : ℕ) ≤ na + nb := by omega
            exact_mod_cast this
        _ ≤ W * (a / W + b / W) + (a % W ♯ b % W) := le_self_add
    · refine h1.trans_lt ?_
      rw [heq]
      have hrlt : a' % W < a % W := by
        have e1 : W * (a / W) + a % W = a := Ordinal.div_add_mod a W
        have e2 : W * (a' / W) + a' % W = a' := Ordinal.div_add_mod a' W
        rw [heq] at e2
        have h3 : W * (a / W) + a' % W < W * (a / W) + a % W := by rw [e1, e2]; exact ha'
        exact lt_of_add_lt_add_left h3
      exact add_lt_add_right (Ordinal.nadd_lt_nadd_right hrlt _) _
  · intro b' hb'
    have h1 := IHb b' hb' ha (hb'.trans hb)
    have hq : b' / W ≤ b / W := Ordinal.div_le_left hb'.le _
    rcases lt_or_eq_of_le hq with hlt | heq
    · refine h1.trans_lt ?_
      have hr : a % W ♯ b' % W < W := hCl _ _ (Ordinal.mod_lt _ hW) (Ordinal.mod_lt _ hW)
      obtain ⟨nb', hnb'⟩ := Ordinal.lt_omega0.1 (hlt.trans hqb)
      have hlt' : nb' < nb := by rw [hnb', hnb] at hlt; exact_mod_cast hlt
      calc W * (a / W + b' / W) + (a % W ♯ b' % W)
          < W * (a / W + b' / W) + W := add_lt_add_right hr _
        _ = W * (a / W + b' / W + 1) := by rw [mul_add_one]
        _ ≤ W * (a / W + b / W) := by
            refine mul_le_mul_right ?_ W
            rw [hna, hnb, hnb']
            have : (na + nb' + 1 : ℕ) ≤ na + nb := by omega
            exact_mod_cast this
        _ ≤ W * (a / W + b / W) + (a % W ♯ b % W) := le_self_add
    · refine h1.trans_lt ?_
      rw [heq]
      have hrlt : b' % W < b % W := by
        have e1 : W * (b / W) + b % W = b := Ordinal.div_add_mod b W
        have e2 : W * (b' / W) + b' % W = b' := Ordinal.div_add_mod b' W
        rw [heq] at e2
        have h3 : W * (b / W) + b' % W < W * (b / W) + b % W := by rw [e1, e2]; exact hb'
        exact lt_of_add_lt_add_left h3
      exact add_lt_add_right (Ordinal.nadd_lt_nadd_left hrlt _) _

/-- If `W` is closed under natural addition, then so is `W * ω`. -/
