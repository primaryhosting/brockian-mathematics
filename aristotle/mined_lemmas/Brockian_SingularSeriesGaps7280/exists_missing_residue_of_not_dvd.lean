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

theorem exists_missing_residue_of_not_dvd (H : Finset ℤ) (p : ℕ)
    (hp : ∀ h ∈ H, ¬ ((p : ℤ) ∣ h)) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  refine ⟨0, fun h hh hcon => hp h hh ?_⟩
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd h p).mp hcon

/-- **Admissible gap ranges from arithmetic progressions with primorial common difference.**
For any `k` and any integer `a` prime to all primes `p ≤ k`, the `k`-term arithmetic progression
`a, a + k#, a + 2·k#, …, a + (k-1)·k#` (common difference the primorial `k#`) is an admissible
tuple. -/
