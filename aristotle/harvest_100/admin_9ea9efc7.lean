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
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ s ≠ 1 ∧ ¬∃ n : ℕ, s = -2 * (n + 1)

/-- The Riemann hypothesis: every nontrivial zero of `ζ` has real part `1/2`.
This is the statement only; it is an open problem and is *not* proved here. -/
def RH : Prop := ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2

/-- This formalisation of the Riemann hypothesis agrees with Mathlib's. -/
theorem RH_iff_RiemannHypothesis : RH ↔ RiemannHypothesis := by
  constructor
  · intro h s hz htriv hne
    exact h s ⟨hz, hne, htriv⟩
  · intro h s hs
    exact h s hs.1 hs.2.2 hs.2.1

/-- Outside the closed critical strip (to the left), `ζ` has no zeros other than the trivial
ones: if `Re s ≤ 0`, `s ≠ 0` and `s` is not a trivial zero, then `ζ s ≠ 0`. -/
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
theorem re_mem_critical_strip {s : ℂ} (hs : IsNontrivialZero s) : 0 < s.re ∧ s.re < 1 := by
  obtain ⟨hz, -, htriv⟩ := hs
  constructor
  · by_contra h
    push_neg at h
    have h0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hz
      norm_num at hz
    exact zeta_ne_zero_of_re_nonpos h h0 htriv hz
  · by_contra h
    push_neg at h
    exact riemannZeta_ne_zero_of_one_le_re h hz

/-- The nontrivial zeros are symmetric about the critical line: `s ↦ 1 - s`. -/
theorem isNontrivialZero_one_sub {s : ℂ} (hs : IsNontrivialZero s) :
    IsNontrivialZero (1 - s) := by
  obtain ⟨h0, h1⟩ := re_mem_critical_strip hs
  have hsn : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n h
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have key := riemannZeta_one_sub hsn hs.2.1
  refine ⟨by rw [key, hs.1]; ring, ?_, ?_⟩
  · intro h
    have hs0 : s = 0 := by linear_combination -h
    rw [hs0] at h0; simp at h0
  · rintro ⟨n, hn⟩
    have hre : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    have h2 : (1 - s).re = 1 - s.re := by simp
    rw [hn, hre] at h2
    have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

/-- **A Lean-checked reduction of the Riemann hypothesis.**

The following are equivalent:
1. Mathlib's `RiemannHypothesis`;
2. every nontrivial zero of `ζ` has real part `1/2`;
3. no nontrivial zero of `ζ` lies strictly to the right of the critical line;
4. no nontrivial zero of `ζ` lies strictly to the left of the critical line.

The equivalence of (2) with (3) and (4) is the reduction of RH to a half-plane statement; it
rests on the functional equation, which makes the set of nontrivial zeros invariant under
`s ↦ 1 - s`. (RH itself is open and is not proved here.) -/
theorem RH_statement :
    [ RiemannHypothesis
    , ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2
    , ∀ s : ℂ, IsNontrivialZero s → s.re ≤ 1 / 2
    , ∀ s : ℂ, IsNontrivialZero s → 1 / 2 ≤ s.re ].TFAE := by
  tfae_have 1 ↔ 2 := RH_iff_RiemannHypothesis.symm
  tfae_have 2 → 3 := fun h s hs => (h s hs).le
  tfae_have 2 → 4 := fun h s hs => (h s hs).ge
  tfae_have 3 → 2 := by
    intro h s hs
    have h1 := h s hs
    have h2 := h (1 - s) (isNontrivialZero_one_sub hs)
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith
  tfae_have 4 → 2 := by
    intro h s hs
    have h1 := h s hs
    have h2 := h (1 - s) (isNontrivialZero_one_sub hs)
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith
  tfae_finish

end Frontier

-- Axiom check for the target theorem.
#print axioms Frontier.RH_statement

