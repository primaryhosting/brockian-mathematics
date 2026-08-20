/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle of `ℂ`,
indexed by `k : ZMod n`. -/

lemma exp_nat_congr (hn : 0 < n) {a b : ℕ} (h : (a : ZMod n) = (b : ZMod n)) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (n : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) / (n : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hmod : a ≡ b [MOD n] := (ZMod.natCast_eq_natCast_iff a b n).mp h
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd (n := n) (a := a) (b := b)).mp hmod
  have hac : (b : ℂ) - (a : ℂ) = (n : ℂ) * (c : ℂ) := by
    exact_mod_cast congrArg (fun t : ℤ => (t : ℂ)) hc
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-c, ?_⟩
  have key : (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) / (n : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ)
          + ((-c : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ)) / (n : ℂ) := by
    congr 1
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * hac
  rw [key, add_div, mul_div_assoc, mul_div_assoc]
  field_simp

