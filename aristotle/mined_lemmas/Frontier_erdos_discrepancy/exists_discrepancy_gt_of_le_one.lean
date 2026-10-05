/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The discrepancy sum of the sequence `f` along the homogeneous arithmetic progression
of common difference `d` and length `n`, i.e. `f d + f (2 d) + ... + f (n d)`. -/

theorem exists_discrepancy_gt_of_le_one (f : ℕ → ℤ) (hf : IsPMOne f) (C : ℤ) (hC : C ≤ 1) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ C < |apSum f d n| := by
  obtain ⟨d, n, hd, hn, -, hlt⟩ := erdos_discrepancy f hf
  exact ⟨d, n, hd, hn, lt_of_le_of_lt hC hlt⟩

/-- The `±1` sequence `1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1` (extended by `1`), which
has discrepancy at most `1` on every homogeneous progression using indices `≤ 11`. -/
