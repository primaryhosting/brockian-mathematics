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

(The header block is placed immediately after the single `import Mathlib` line, since Lean 4
requires `import` commands to precede any module docstring.)
-/

open Complex

namespace Frontier

/-- `s` is a *nontrivial zero* of the Riemann zeta function: a zero of `ζ` which is neither
the pole `s = 1` (where Mathlib's `riemannZeta` takes a junk value) nor one of the trivial
zeros `s = -2, -4, -6, …`. -/

theorem zeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) (h0 : s ≠ 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : riemannZeta s ≠ 0 := by
  set w : ℂ := 1 - s with hw
  have hwre : 1 ≤ w.re := by
    simp only [hw, Complex.sub_re, Complex.one_re]; linarith
  have hwn : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n h
    rw [h] at hwre
    simp only [Complex.neg_re, Complex.natCast_re] at hwre
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hw1 : w ≠ 1 := by
    intro h
    apply h0
    have hs2 : s = 1 - w := by rw [hw]; ring
    rw [hs2, h]; ring
  have key := riemannZeta_one_sub hwn hw1
  have hsw : (1 : ℂ) - w = s := by rw [hw]; ring
  rw [hsw] at key
  rw [key]
  have hcos : Complex.cos ((Real.pi : ℂ) * w / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hwk : w = 2 * (k : ℂ) + 1 := by field_simp at hk; exact hk
    have hre : w.re = 2 * (k : ℝ) + 1 := by rw [hwk]; simp
    have hk0 : 0 ≤ k := by
      have h' : (0:ℝ) ≤ (k:ℝ) := by rw [hre] at hwre; linarith
      exact_mod_cast h'
    have hs' : s = -2 * (k : ℂ) := by rw [← hsw, hwk]; ring
    rcases eq_or_lt_of_le hk0 with h | h
    · exact h0 (by rw [hs', ← h]; simp)
    · apply htriv
      refine ⟨(k - 1).toNat, ?_⟩
      have hc2 : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
        have h3 : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h3
      rw [hs', hc2]; ring
  have hbase : ((2 : ℂ) * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have h1 : ((2 : ℂ) * (Real.pi : ℂ)) ^ (-w) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  have h2 : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwn
  have h3 : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  simp [h1, h2, h3, hcos]

/-- Nontrivial zeros lie in the open critical strip. -/
