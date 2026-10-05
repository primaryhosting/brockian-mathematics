import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter Asymptotics
open scoped Classical

namespace Math2

variable {n : ℕ}

/-- A subset of `𝔽₃ⁿ` is a *cap set* if it contains no line, i.e. no three points summing to
zero other than the degenerate ones `x + x + x = 0`.  Equivalently (see
`Math2.threeAPFree_of_isCapSet`) it contains no nontrivial three-term arithmetic progression. -/

theorem capSetNumber_isLittleO :
    IsLittleO atTop (fun n : ℕ => (capSetNumber n : ℝ)) (fun n : ℕ => (3 : ℝ) ^ n) := by
  rw [isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := cap_set ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨A, hA, hAeq⟩ := exists_capSetNumber n
  have h := hN n hn A hA
  rw [hAeq, Real.norm_natCast, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ n)]
  exact h

end Math2

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

