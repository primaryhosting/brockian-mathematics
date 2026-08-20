import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The cosine coordinate of the `k`-th "isotypic" vector for the regular `n`-gon:
the function `m ↦ cos (2πkm/n)` on the vertices `m` of the `n`-gon. -/

lemma ngonRoot_ne_one (n : ℕ) (k : ℤ) (hn : n ≠ 0) (hk : ¬ ((n : ℤ) ∣ k)) :
    ngonRoot n k ≠ 1 := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  intro h
  rw [ngonRoot, Complex.exp_eq_one_iff] at h
  obtain ⟨j, hj⟩ := h
  rw [div_eq_iff hn'] at hj
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I) * ((j : ℂ) * n) := by linear_combination hj
  have hkz : k = j * n := by exact_mod_cast mul_left_cancel₀ hne h2
  exact hk ⟨j, by rw [hkz]; ring⟩

