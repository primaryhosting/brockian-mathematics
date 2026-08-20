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

theorem card_primorial_progression (k : ℕ) (a : ℤ) :
    ((Finset.range k).image (fun i : ℕ => a + (i : ℤ) * (primorial k : ℤ))).card = k := by
  have hpos : (0 : ℤ) < (primorial k : ℤ) := by
    exact_mod_cast primorial_pos k
  have hinj : Set.InjOn (fun i : ℕ => a + (i : ℤ) * (primorial k : ℤ))
      (Finset.range k : Finset ℕ) := by
    intro i _ j _ hij
    simp only at hij
    have h : (i : ℤ) * (primorial k : ℤ) = (j : ℤ) * (primorial k : ℤ) := by linarith
    have := mul_right_cancel₀ (ne_of_gt hpos) h
    exact_mod_cast this
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-- **Singular Series Gaps 7280.**
A new family of admissible gap ranges of length `7280`: for every integer `a` that is prime to
all primes `p ≤ 7280`, the `7280`-term arithmetic progression with common difference the
primorial `7280#`,
`a, a + 7280#, a + 2·7280#, …, a + 7279·7280#`,
consists of `7280` distinct integers and is an admissible tuple, i.e. for every prime `p` it
omits a residue class modulo `p`.  Consequently its Hardy–Littlewood singular series is nonzero. -/
