/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The cap-set bound: subsets of `𝔽₃ⁿ` with no three-term arithmetic progression have size
`o(3ⁿ)`.  This is the Croot–Lev–Pach / Ellenberg–Gijswijt theorem, proved here by the
polynomial method.
-/

open Finset

namespace Math2
namespace CapSet

instance factThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The field `𝔽₃`. -/
abbrev F := ZMod 3

/-- The vector space `𝔽₃ⁿ`. -/
abbrev V (n : ℕ) := Fin n → F

/-- Exponent vectors of reduced monomials: each exponent is `0`, `1` or `2`. -/
abbrev E (n : ℕ) := Fin n → Fin 3

/-- Total degree of a reduced monomial. -/

theorem cap_set_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Fin n → ZMod 3),
      ThreeAPFree (A : Set (Fin n → ZMod 3)) → (A.card : ℝ) ≤ ε * 3 ^ n := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 CapSet.capSetMax_div_tendsto ε hε
  refine ⟨N, fun n hn A hA => ?_⟩
  have h1 : (A.card : ℝ) ≤ (CapSet.capSetMax n : ℝ) := by
    exact_mod_cast CapSet.le_capSetMax A hA
  have h2 := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
  have h3 : (CapSet.capSetMax n : ℝ) ≤ ε * 3 ^ n := by
    rw [← div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ n)] at *
    exact le_of_lt h2
  linarith

end Math2

import Mathlib
import RequestProject.CapSet

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

