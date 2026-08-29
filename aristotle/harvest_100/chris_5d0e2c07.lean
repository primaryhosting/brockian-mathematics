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
# Continuum Eq Two Pow Aleph 0
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.continuum_eq_two_pow_aleph0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Cardinal

/-- The cardinality of the continuum equals `2 ^ ℵ₀`.

In Mathlib `Cardinal.continuum` is *defined* as `2 ^ ℵ₀`, so this is the
identity witnessed by `Cardinal.two_power_aleph0`. -/
theorem continuum_eq_two_pow_aleph0 : Cardinal.continuum = 2 ^ Cardinal.aleph0 :=
  Cardinal.two_power_aleph0.symm

/-!
## The substantive statement: `#ℝ = 2 ^ ℵ₀`

Below we give a self-contained two-sided proof (not appealing to
`Cardinal.mk_real`), by exhibiting explicit injections in both directions.
-/

/-- Sending a real number to the set of rationals strictly below it is injective. -/
theorem injective_ratsBelow :
    Function.Injective (fun r : ℝ => {q : ℚ | (q : ℝ) < r}) := by
  intro r s hrs
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
    have hq := Set.ext_iff.mp hrs q
    simp only [Set.mem_setOf_eq] at hq
    exact absurd (hq.mpr hq2) (not_lt.mpr hq1.le)
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
    have hq := Set.ext_iff.mp hrs q
    simp only [Set.mem_setOf_eq] at hq
    exact absurd (hq.mp hq2) (not_lt.mpr hq1.le)

/-- Upper bound: `#ℝ ≤ 2 ^ ℵ₀`, via the Dedekind-cut embedding `ℝ ↪ Set ℚ`. -/
theorem mk_real_le_two_pow_aleph0 :
    Cardinal.mk ℝ ≤ 2 ^ Cardinal.aleph0 := by
  have h1 : Cardinal.mk ℝ ≤ Cardinal.mk (Set ℚ) :=
    Cardinal.mk_le_of_injective injective_ratsBelow
  have h2 : Cardinal.mk (Set ℚ) = 2 ^ Cardinal.mk ℚ := Cardinal.mk_set
  rw [h2, Cardinal.mk_denumerable ℚ] at h1
  exact h1

/-- Lower bound: `2 ^ ℵ₀ ≤ #ℝ`, via the Cantor function `(ℕ → Bool) ↪ ℝ`. -/
theorem two_pow_aleph0_le_mk_real :
    (2 : Cardinal) ^ Cardinal.aleph0 ≤ Cardinal.mk ℝ := by
  have hinj : Function.Injective (Cardinal.cantorFunction (1 / 3)) :=
    Cardinal.cantorFunction_injective (by norm_num) (by norm_num)
  have h1 : Cardinal.mk (ℕ → Bool) ≤ Cardinal.mk ℝ :=
    Cardinal.mk_le_of_injective hinj
  have h2 : Cardinal.mk (ℕ → Bool) = 2 ^ Cardinal.aleph0 := by
    rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat]
    simp
  rwa [h2] at h1

/-- The cardinality of the real numbers equals `2 ^ ℵ₀`. -/
theorem mk_real_eq_two_pow_aleph0 :
    Cardinal.mk ℝ = 2 ^ Cardinal.aleph0 :=
  le_antisymm mk_real_le_two_pow_aleph0 two_pow_aleph0_le_mk_real

/-- Consequently `#ℝ = 𝔠`. -/
theorem mk_real_eq_continuum : Cardinal.mk ℝ = Cardinal.continuum :=
  mk_real_eq_two_pow_aleph0.trans continuum_eq_two_pow_aleph0.symm

end Cardinal

