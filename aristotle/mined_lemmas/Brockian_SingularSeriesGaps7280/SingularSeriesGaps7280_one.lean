/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
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

/-- A finite set `H` of integers is *admissible* if for every prime `p` the elements of `H`
do not cover all residue classes modulo `p`.  This is exactly the condition under which the
Hardy–Littlewood singular series `𝔖(H)` of the tuple `H` is nonzero. -/

theorem SingularSeriesGaps7280_one :
    ((Finset.range 7280).image (fun i : ℕ => 1 + (i : ℤ) * (primorial 7280 : ℤ))).card = 7280 ∧
      Admissible ((Finset.range 7280).image (fun i : ℕ => 1 + (i : ℤ) * (primorial 7280 : ℤ))) := by
  refine SingularSeriesGaps7280 1 ?_
  intro p hp _ hdvd
  have h1 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
  have h2 : 2 ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  linarith

end Brockian

