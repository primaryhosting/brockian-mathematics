import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace Frontier

/-- `s` is a *nontrivial zero* of the Riemann zeta function if `ζ s = 0` and `s` is not one of
the *trivial zeros* `-2, -4, -6, …`. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ ∀ n : ℕ, s ≠ -2 * (n + 1)

/-- **The Riemann Hypothesis**: every nontrivial zero of `ζ` has real part `1 / 2`. -/
def RiemannHypothesisStatement : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2

/-- The trivial zeros really are zeros: `ζ (-2 (n+1)) = 0`. -/
theorem zeta_neg_two_mul_nat_add_one_eq_zero (n : ℕ) : riemannZeta (-2 * (n + 1 : ℂ)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n

/-- `ζ` does not vanish at the negative odd integers: this uses the functional equation to
transfer nonvanishing from `re s ≥ 1`. -/
theorem zeta_neg_odd_ne_zero (k : ℕ) : riemannZeta (-(2 * (k : ℂ) + 1)) ≠ 0 := by
  have hre : (2 * (k : ℂ) + 2).re = 2 * k + 2 := by simp
  have hs1 : ∀ n : ℕ, (2 * (k : ℂ) + 2) ≠ -n := by
    intro n h
    have h2 := congrArg Complex.re h
    rw [hre] at h2
    simp at h2
    nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) n]
  have hs2 : (2 * (k : ℂ) + 2) ≠ 1 := by
    intro h
    have h2 := congrArg Complex.re h
    rw [hre] at h2
    simp at h2
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have key := riemannZeta_one_sub hs1 hs2
  have h1s : (1 : ℂ) - (2 * (k : ℂ) + 2) = -(2 * (k : ℂ) + 1) := by ring
  rw [h1s] at key
  rw [key]
  have hcos : Complex.cos ((Real.pi : ℂ) * (2 * (k : ℂ) + 2) / 2) = ((-1 : ℝ) ^ (k + 1) : ℝ) := by
    have h : (Real.pi : ℂ) * (2 * (k : ℂ) + 2) / 2 = ((((k + 1 : ℕ) : ℝ) * Real.pi : ℝ) : ℂ) := by
      push_cast; ring
    rw [h, ← Complex.ofReal_cos, Real.cos_nat_mul_pi]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_) ?_
  · rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨two_ne_zero, by exact_mod_cast Real.pi_ne_zero⟩)
  · exact Complex.Gamma_ne_zero hs1
  · rw [hcos]; simp
  · refine riemannZeta_ne_zero_of_one_le_re ?_
    rw [hre]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- A nontrivial zero is never a nonpositive integer. -/
theorem IsNontrivialZero.ne_neg_nat {s : ℂ} (hs : IsNontrivialZero s) (n : ℕ) : s ≠ -n := by
  obtain ⟨hz, htriv⟩ := hs
  rintro rfl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, neg_zero, riemannZeta_zero] at hz
    norm_num at hz
  · rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨k, hk⟩
    · have hj1 : (j - 1 : ℕ) + 1 = j := by omega
      refine htriv (j - 1) ?_
      have hcast : ((n : ℂ)) = 2 * (((j - 1 : ℕ) : ℂ) + 1) := by
        rw [show ((j - 1 : ℕ) : ℂ) + 1 = ((j : ℕ) : ℂ) by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) hj1]
        rw [hj]; push_cast; ring
      rw [hcast]; ring
    · exact absurd hz (by
        rw [show (-(n : ℂ)) = -(2 * (k : ℂ) + 1) by rw [hk]; push_cast; ring]
        exact zeta_neg_odd_ne_zero k)

/-- A nontrivial zero is not `1` (with Mathlib's conventions, `ζ 1 ≠ 0`). -/
theorem IsNontrivialZero.ne_one {s : ℂ} (hs : IsNontrivialZero s) : s ≠ 1 := by
  rintro rfl
  exact riemannZeta_one_ne_zero hs.1

/-- The zeros of `ζ` are symmetric about the critical line: if `s` is a nontrivial zero then so
is `1 - s`. -/
theorem IsNontrivialZero.one_sub {s : ℂ} (hs : IsNontrivialZero s) :
    IsNontrivialZero (1 - s) := by
  have hzero : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_one_sub hs.ne_neg_nat hs.ne_one, hs.1, mul_zero]
  refine ⟨hzero, ?_⟩
  intro n hn
  have hsval : s = 2 * n + 3 := by
    have h : (1 : ℂ) - s = -2 * (n + 1) := hn
    linear_combination -h
  have hre : (1 : ℝ) ≤ s.re := by
    rw [hsval]
    simp
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact riemannZeta_ne_zero_of_one_le_re hre hs.1

/-- Every nontrivial zero lies in the open critical strip `0 < re s < 1`. -/
theorem IsNontrivialZero.re_mem_Ioo {s : ℂ} (hs : IsNontrivialZero s) :
    0 < s.re ∧ s.re < 1 := by
  have h1 : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hs.1
  have h2 := hs.one_sub
  have h3 : (1 - s).re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) h2.1
  simp only [Complex.sub_re, Complex.one_re] at h3
  exact ⟨by linarith, h1⟩

/-- **A Lean-checked reduction of the Riemann Hypothesis.**
The Riemann Hypothesis — all nontrivial zeros of `ζ` have real part `1/2` — holds if and only if
`ζ` has no zero in the open right half `1/2 < re s < 1` of the critical strip.

The nontrivial content is the reverse implication, which combines the nonvanishing of `ζ` on
`re s ≥ 1`, the nonvanishing at the nonpositive integers other than the trivial zeros, and the
functional equation `ζ (1 - s) = 2 (2π)^{-s} Γ(s) cos(πs/2) ζ(s)`, which makes the set of
nontrivial zeros invariant under `s ↦ 1 - s`. -/
theorem RH_statement :
    RiemannHypothesisStatement ↔ ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  constructor
  · intro h s hlt hlt' hz
    have hnt : IsNontrivialZero s := by
      refine ⟨hz, fun n hn => ?_⟩
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      simp only [hn, Complex.mul_re] at hlt
      norm_num at hlt
      linarith
    exact absurd (h s hnt) (by linarith)
  · intro h s hs
    obtain ⟨h0, h1⟩ := hs.re_mem_Ioo
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · have h2 := hs.one_sub
      obtain ⟨h2', h2''⟩ := h2.re_mem_Ioo
      have hre : (1 - s).re = 1 - s.re := by simp
      exact absurd h2.1 (h (1 - s) (by rw [hre]; linarith) h2'')
    · exact heq
    · exact absurd hs.1 (h s hgt h1)

/-- Our formulation of the Riemann Hypothesis agrees with Mathlib's `RiemannHypothesis`. -/
theorem RH_statement_iff_mathlib : RiemannHypothesisStatement ↔ RiemannHypothesis := by
  constructor
  · intro h s hz hnt _
    exact h s ⟨hz, fun n hn => hnt ⟨n, hn⟩⟩
  · intro h s hs
    exact h s hs.1 (fun ⟨n, hn⟩ => hs.2 n hn) hs.ne_one

end Frontier

-- Axiom check (should list only `propext`, `Classical.choice`, `Quot.sound`).
#print axioms Frontier.RH_statement
#print axioms Frontier.RH_statement_iff_mathlib
#print axioms Frontier.IsNontrivialZero.re_mem_Ioo
#print axioms Frontier.zeta_neg_odd_ne_zero

