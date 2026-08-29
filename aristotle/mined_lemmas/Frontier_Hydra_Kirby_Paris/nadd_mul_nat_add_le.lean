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

private theorem nadd_mul_nat_add_le (e : Ordinal.{0}) (he0 : 0 < e)
    (he : ∀ x y : Ordinal.{0}, x < e → y < e → x ♯ y < e) (N : ℕ) :
    ∀ n m : ℕ, n + m = N → ∀ a : Ordinal.{0}, a < e → ∀ b : Ordinal.{0}, b < e →
      (e * (n : Ordinal) + a) ♯ (e * (m : Ordinal) + b) ≤ e * (N : Ordinal) + (a ♯ b) := by
  have hene : e ≠ 0 := ne_of_gt he0
  have hmul_le : ∀ k K : ℕ, k ≤ K → e * (k : Ordinal) ≤ e * (K : Ordinal) := by
    intro k K hk
    exact mul_le_mul_right (by exact_mod_cast hk) e
  have hstep : ∀ k : ℕ, e * ((k : ℕ) : Ordinal) + e = e * ((k + 1 : ℕ) : Ordinal) := by
    intro k
    have h : ((k + 1 : ℕ) : Ordinal) = ((k : ℕ) : Ordinal) + 1 := by push_cast; ring_nf
    rw [h, mul_add, mul_one]
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    intro n m hnm a
    induction a using Ordinal.induction with
    | h a iha =>
      intro ha b
      induction b using Ordinal.induction with
      | h b ihb =>
        intro hb
        rw [Ordinal.nadd_le_iff]
        constructor
        · intro x hx
          obtain ⟨j, x₀, rfl, hx₀, hjn⟩ := nat_decomp e hene n x a ha.le hx
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hjn) with rfl | hjn'
          · have hx₀a : x₀ < a := lt_of_add_lt_add_left hx
            calc (e * (j : Ordinal) + x₀) ♯ (e * (m : Ordinal) + b)
                ≤ e * (N : Ordinal) + (x₀ ♯ b) := iha x₀ hx₀a hx₀ b hb
              _ < e * (N : Ordinal) + (a ♯ b) :=
                  add_lt_add_right (Ordinal.nadd_lt_nadd_right hx₀a b) _
          · have hsum : j + m < N := by omega
            calc (e * (j : Ordinal) + x₀) ♯ (e * (m : Ordinal) + b)
                ≤ e * ((j + m : ℕ) : Ordinal) + (x₀ ♯ b) := ihN (j + m) hsum j m rfl x₀ hx₀ b hb
              _ < e * ((j + m : ℕ) : Ordinal) + e := add_lt_add_right (he _ _ hx₀ hb) _
              _ = e * ((j + m + 1 : ℕ) : Ordinal) := hstep (j + m)
              _ ≤ e * (N : Ordinal) := hmul_le _ _ (by omega)
              _ ≤ e * (N : Ordinal) + (a ♯ b) := le_self_add
        · intro y hy
          obtain ⟨j, y₀, rfl, hy₀, hjm⟩ := nat_decomp e hene m y b hb.le hy
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hjm) with rfl | hjm'
          · have hy₀b : y₀ < b := lt_of_add_lt_add_left hy
            calc (e * (n : Ordinal) + a) ♯ (e * (j : Ordinal) + y₀)
                ≤ e * (N : Ordinal) + (a ♯ y₀) := ihb y₀ hy₀b hy₀
              _ < e * (N : Ordinal) + (a ♯ b) :=
                  add_lt_add_right (Ordinal.nadd_lt_nadd_left hy₀b a) _
          · have hsum : n + j < N := by omega
            calc (e * (n : Ordinal) + a) ♯ (e * (j : Ordinal) + y₀)
                ≤ e * ((n + j : ℕ) : Ordinal) + (a ♯ y₀) := ihN (n + j) hsum n j rfl a ha y₀ hy₀
              _ < e * ((n + j : ℕ) : Ordinal) + e := add_lt_add_right (he _ _ ha hy₀) _
              _ = e * ((n + j + 1 : ℕ) : Ordinal) := hstep (n + j)
              _ ≤ e * (N : Ordinal) := hmul_le _ _ (by omega)
              _ ≤ e * (N : Ordinal) + (a ♯ b) := le_self_add

/-- Powers of `ω` are closed under the natural (Hessenberg) sum. -/
