import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

lemma sum_range_choose_le (N D : ℕ) :
    (∑ k ∈ Finset.range (N + D + 1), (2 * N).choose k)
      ≤ 2 ^ (2 * N) / 2 + (D + 1) * (2 * N).choose N := by
  classical
  have hsplit : ∑ k ∈ Finset.range (N + D + 1), (2 * N).choose k
      = (∑ k ∈ Finset.range N, (2 * N).choose k)
        + ∑ k ∈ Finset.Ico N (N + D + 1), (2 * N).choose k := by
    have h1 : Finset.range (N + D + 1) = Finset.range N ∪ Finset.Ico N (N + D + 1) := by
      ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range N) (Finset.Ico N (N + D + 1)) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ico] at hk'
      omega
    rw [h1, Finset.sum_union hdisj]
  have hlow : 2 * (∑ k ∈ Finset.range N, (2 * N).choose k) ≤ 2 ^ (2 * N) := by
    have := two_mul_sum_range_choose_le N
    have h4 : (4 : ℕ) ^ N = 2 ^ (2 * N) := by rw [pow_mul]; norm_num
    omega
  have hhigh : (∑ k ∈ Finset.Ico N (N + D + 1), (2 * N).choose k)
      ≤ (D + 1) * (2 * N).choose N := by
    have hb : ∀ k ∈ Finset.Ico N (N + D + 1), (2 * N).choose k ≤ (2 * N).choose N := by
      intro k _
      have := Nat.choose_le_middle k (2 * N)
      simpa [Nat.mul_div_cancel_left] using this
    have h := Finset.sum_le_card_nsmul (Finset.Ico N (N + D + 1)) _ ((2 * N).choose N) hb
    rw [Nat.card_Ico, smul_eq_mul] at h
    have hc : N + D + 1 - N = D + 1 := by omega
    rwa [hc] at h
  omega

end CS

import Mathlib

/-!
# Boolean circuits of bounded depth (AC⁰)

A circuit over `n` input variables is a directed acyclic graph of gates.  We
represent it as a finite list of gates `gate : Fin size → Gate n size`, where the
gate at index `i` may only refer to gates at strictly smaller indices (`wf`).
Gates are `const`, `var`, `not`, unbounded fan-in `and` and unbounded fan-in `or`.

The semantics is given by the fixed-point predicate `Circuit.Vals`, which has a
unique solution for every input (`Circuit.vals_unique`, `Circuit.exists_vals`).

The depth of a circuit is measured by *AND/OR gates only* (negations are free),
via the existence of a level labelling; this is the standard notion, and gives
the strongest form of the lower bound.
-/

namespace CS

/-- The Boolean cube: assignments of the `n` input variables. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- A gate of a circuit with `n` inputs, whose predecessors are among `Fin m`. -/
inductive Gate (n m : ℕ) where
  | const (b : Bool)
  | var (i : Fin n)
  | not (j : Fin m)
  | and (s : Finset (Fin m))
  | or (s : Finset (Fin m))

/-- The set of gates a gate refers to. -/
