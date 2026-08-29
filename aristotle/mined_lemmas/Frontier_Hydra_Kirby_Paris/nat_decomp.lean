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

private theorem nat_decomp (e : Ordinal.{0}) (hene : e ≠ 0) (n : ℕ) (x c : Ordinal.{0})
    (hc : c ≤ e) (hx : x < e * (n : Ordinal) + c) :
    ∃ (j : ℕ) (x₀ : Ordinal.{0}), x = e * (j : Ordinal) + x₀ ∧ x₀ < e ∧ j < n + 1 := by
  have hx₀ : x % e < e := Ordinal.mod_lt x hene
  have hxeq : e * (x / e) + x % e = x := Ordinal.div_add_mod x e
  have hklt : x / e < ((n : Ordinal) + 1) := by
    rw [Ordinal.div_lt hene, mul_add, mul_one]
    exact hx.trans_le (add_le_add_right hc _)
  have h1 : ((n + 1 : ℕ) : Ordinal) = (n : Ordinal) + 1 := by push_cast; ring_nf
  obtain ⟨j, hj⟩ := Ordinal.lt_omega0.1 (hklt.trans (h1 ▸ Ordinal.nat_lt_omega0 (n + 1)))
  refine ⟨j, x % e, ?_, hx₀, ?_⟩
  · rw [← hj]; exact hxeq.symm
  · have : (j : Ordinal) < ((n + 1 : ℕ) : Ordinal) := by rw [h1, ← hj]; exact hklt
    exact_mod_cast this

/-- If `e` is closed under natural sums, then natural sums add the "digits" of the
multiples of `e`: `(e * n + a) ♯ (e * m + b) ≤ e * (n + m) + (a ♯ b)`. -/
