/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring before the `import` line; the required
header is reproduced verbatim below as the module docstring.)
-/

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open Finset Set

/-! ## Finite games in normal form -/

section Defs

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The set of mixed strategy profiles of a finite game: for each player `i` a probability
distribution on that player's (finite) pure strategy set `S i`. -/

lemma isNash_of_fixed {x : ∀ i, S i → ℝ} (hx : x ∈ mixedProfiles S)
    (hfix : nashMap u x = x) : IsMixedNashEquilibrium u x := by
  refine ⟨hx, ?_⟩
  intro i y hy
  have hxi : x i ∈ stdSimplex ℝ (S i) := hx i (Set.mem_univ i)
  set c : ℝ := ∑ t, max 0 (gain u x i t) with hc
  have hcnonneg : 0 ≤ c := Finset.sum_nonneg fun t _ => le_max_left _ _
  have hden : (0:ℝ) < 1 + c := by linarith
  have hkey : ∀ s, x i s * c = max 0 (gain u x i s) := by
    intro s
    have h := congrFun (congrFun hfix i) s
    unfold nashMap at h
    rw [← hc, div_eq_iff (ne_of_gt hden)] at h
    nlinarith [h]
  have hzero : ∑ s, x i s * gain u x i s = 0 := by
    simp only [gain, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hxi.2, one_mul,
      ← expectedPayoff_eq_sum, sub_self]
  have hc0 : c = 0 := by
    by_contra hne
    have hcpos : 0 < c := lt_of_le_of_ne hcnonneg (Ne.symm hne)
    have hterm : ∀ s ∈ Finset.univ, 0 ≤ x i s * gain u x i s := by
      intro s _
      rcases eq_or_lt_of_le (hxi.1 s) with h | h
      · rw [← h]; simp
      · have hm : 0 < max 0 (gain u x i s) := by
          rw [← hkey s]; positivity
        have : 0 < gain u x i s := by
          rcases max_cases 0 (gain u x i s) with ⟨he, _⟩ | ⟨he, hle⟩
          · rw [he] at hm; exact absurd hm (lt_irrefl 0)
          · rw [he] at hm; exact hm
        positivity
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hzero
    have hzeros : ∀ s, x i s = 0 := by
      intro s
      by_contra hs
      have hpos : 0 < x i s := lt_of_le_of_ne (hxi.1 s) (Ne.symm hs)
      have hg : gain u x i s = 0 := by
        have := hall s (Finset.mem_univ s)
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (ne_of_gt hpos)
        · exact h
      have hm : 0 < max 0 (gain u x i s) := by rw [← hkey s]; positivity
      rw [hg] at hm
      simp at hm
    have := hxi.2
    rw [Finset.sum_congr rfl fun s _ => hzeros s] at this
    simp at this
  have hgain : ∀ s, gain u x i s ≤ 0 := by
    intro s
    have := hkey s
    rw [hc0, mul_zero] at this
    have h2 : gain u x i s ≤ max 0 (gain u x i s) := le_max_right _ _
    linarith [this ▸ h2]
  rw [expectedPayoff_update]
  have hle : ∀ s ∈ Finset.univ,
      y s * expectedPayoff u (Function.update x i (Pi.single s 1)) i
        ≤ y s * expectedPayoff u x i := by
    intro s _
    have := hgain s
    unfold gain at this
    exact mul_le_mul_of_nonneg_left (by linarith) (hy.1 s)
  calc ∑ s, y s * expectedPayoff u (Function.update x i (Pi.single s 1)) i
      ≤ ∑ s, y s * expectedPayoff u x i := Finset.sum_le_sum hle
    _ = expectedPayoff u x i := by rw [← Finset.sum_mul, hy.2, one_mul]

/-- **Nash's theorem** (a Lean-checked reduction to Brouwer's fixed point theorem).
Every finite game in normal form — a finite set of players `ι`, a nonempty finite set of pure
strategies `S i` for each player, and an arbitrary real payoff function `u i` on pure strategy
profiles — has a mixed-strategy Nash equilibrium, given Brouwer's fixed point theorem. -/
