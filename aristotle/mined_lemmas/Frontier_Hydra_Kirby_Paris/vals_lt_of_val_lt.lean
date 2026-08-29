import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Statement: Every hydra game terminates for any strategy (Kirby–Paris).

A hydra is a finite rooted tree.  Hercules repeatedly cuts off a head (a leaf).
If the head is at depth `1` (a child of the root) it simply disappears.  Otherwise
the head is removed from its parent `p` and then an arbitrary finite number `n` of
extra copies of the (already shortened) subtree `p` are attached to the grandparent
of the head.  The Kirby–Paris theorem says that whatever the strategy is — that is,
whichever head is chosen at each turn and however many copies grow back — the hydra
is eventually reduced to the single node `dead = node []`.

The proof below is the usual ordinal assignment: a hydra is mapped to an ordinal
below `ε₀` by `val (node [t₁, …, t_k]) = ω ^ val t₁ ♯ … ♯ ω ^ val t_k`, where `♯`
is the natural (Hessenberg) sum, and each move is shown to strictly decrease this
ordinal.

The key ordinal fact needed — that `ω ^ c` is closed under natural sums — is not in
Mathlib, so it is proved here (`Frontier.nadd_lt_opow_omega0`).
-/

open Ordinal
open scoped NaturalOps

namespace Frontier

/-! ### Natural sums are bounded by powers of `ω` -/

/-- Every `x` below `e * n + c` (with `c ≤ e`) is of the form `e * j + x₀` with `x₀ < e`
and `j ≤ n`. -/

theorem vals_lt_of_val_lt {t t' : Hydra} (l₁ l₂ : List Hydra) (h : val t' < val t) :
    vals (l₁ ++ t' :: l₂) < vals (l₁ ++ t :: l₂) := by
  have hpow : (ω : Ordinal) ^ val t' < ω ^ val t :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 h
  simp only [vals_append, vals_cons]
  exact Ordinal.nadd_lt_nadd_left (Ordinal.nadd_lt_nadd_right hpow _) _

/-- Replacing an element of a list of hydras by a list of hydras of small total value
decreases the value. -/
