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

/-
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` lines to come first, so the required header block
appears at the very top of the file as a plain comment and is repeated verbatim as the module
docstring immediately after `import Mathlib`.

What is discharged here: the functional-equation ("reflection of zeros") sub-lemma
`zeta_reflect_zero`, which is proved from Mathlib's `riemannZeta_one_sub`, together with the
classification of the zeros with `Re s ≤ 0` as the trivial ones.  The remaining input of the
main theorem is the Brockian non-vanishing system itself.
-/

open Complex

namespace Brockian
namespace RiemannScaffold

/-- A *Brockian system* is a witness for the non-vanishing of the Riemann zeta function
on the right half `1/2 < Re s < 1` of the critical strip. -/
structure BrockianSystem : Prop where
  /-- `ζ` has no zero with `1/2 < Re s < 1`. -/
  nonvanishing_right : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0

/-- **Discharged hypothesis (reflection of zeros).**  Originally this was a named hypothesis of
`RH_of_BrockianSystem`; it is discharged here from Mathlib's functional equation
`riemannZeta_one_sub`. -/
theorem zeta_reflect_zero {s : ℂ} (hn : ∀ n : ℕ, s ≠ -n) (h1 : s ≠ 1)
    (hz : riemannZeta s = 0) : riemannZeta (1 - s) = 0 := by
  rw [riemannZeta_one_sub hn h1, hz, mul_zero]

/-- If `Re s > 1` and `ζ (1 - s) = 0`, then `1 - s = -2 * (n + 1)` for some `n : ℕ`.
This isolates the trivial zeros. -/
theorem trivial_zero_of_re_lt_zero {s : ℂ} (hs : 1 < s.re) (hz : riemannZeta (1 - s) = 0) :
    ∃ n : ℕ, (1 - s) = -2 * (n + 1) := by
  have hn : ∀ n : ℕ, s ≠ -n := by
    intro n h
    rw [h] at hs
    simp at hs
    linarith [hs, Nat.cast_nonneg (α := ℝ) n]
  have h1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  rw [riemannZeta_one_sub hn h1] at hz
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hpow : ((2 : ℂ) * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by simp [hpi])
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h3 | h3
          · norm_num at h3
          · exact absurd h3 hpow
        · exact absurd h'' hΓ
      · exact h'
    · exact absurd h hζ
  rw [Complex.cos_eq_zero_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  have hs_eq : s = 2 * (k : ℂ) + 1 := by
    field_simp at hk
    linear_combination hk
  have hkre : (1 : ℝ) < 2 * (k : ℝ) + 1 := by
    have hsre : s.re = 2 * (k : ℝ) + 1 := by rw [hs_eq]; simp
    linarith [hsre ▸ hs]
  have hk1 : 1 ≤ k := by
    have h0 : (0 : ℝ) < (k : ℝ) := by linarith
    exact_mod_cast (by exact_mod_cast h0 : (0 : ℤ) < k)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  refine ⟨m, ?_⟩
  rw [hs_eq, hm]
  push_cast
  ring

/-- **Main theorem.**  A Brockian system implies the Riemann Hypothesis (in Mathlib's
formulation: every zero of `ζ` other than the trivial zeros `-2(n+1)` and the point `1`
lies on the critical line). -/
theorem RH_of_BrockianSystem (B : BrockianSystem) : RiemannHypothesis := by
  intro s hz hntriv hs1
  by_contra hre
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1 hz
  push_neg at h1
  have hsub : (1 - s).re = 1 - s.re := by simp
  by_cases h0 : 0 < s.re
  · -- inside the critical strip
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · -- reflect to the right half of the strip
      have hn : ∀ n : ℕ, s ≠ -n := by
        intro n h
        rw [h] at h0
        simp only [Complex.neg_re, Complex.natCast_re] at h0
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have hz' : riemannZeta (1 - s) = 0 := zeta_reflect_zero hn hs1 hz
      exact B.nonvanishing_right (1 - s) (by rw [hsub]; linarith) (by rw [hsub]; linarith) hz'
    · exact hre heq
    · exact B.nonvanishing_right s hgt h1 hz
  push_neg at h0
  rcases eq_or_lt_of_le h0 with h0' | h0'
  · -- `Re s = 0`
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [riemannZeta_zero] at hz; norm_num at hz
    · have hn : ∀ n : ℕ, s ≠ -n := by
        intro n h
        apply hs0
        rw [h] at h0'
        simp only [Complex.neg_re, Complex.natCast_re] at h0'
        have hnr : (n : ℝ) = 0 := by linarith
        have hn0 : n = 0 := by exact_mod_cast hnr
        rw [h, hn0]; simp
      have hz' : riemannZeta (1 - s) = 0 := zeta_reflect_zero hn hs1 hz
      have hre1 : (1 : ℝ) ≤ (1 - s).re := by rw [hsub]; linarith
      exact riemannZeta_ne_zero_of_one_le_re hre1 hz'
  · -- `Re s < 0`: `s` must be a trivial zero
    apply hntriv
    have hkey : ∃ n : ℕ, (1 - (1 - s)) = -2 * (n + 1) := by
      refine trivial_zero_of_re_lt_zero (s := 1 - s) ?_ ?_
      · rw [hsub]; linarith
      · simpa using hz
    simpa using hkey

end RiemannScaffold
end Brockian

