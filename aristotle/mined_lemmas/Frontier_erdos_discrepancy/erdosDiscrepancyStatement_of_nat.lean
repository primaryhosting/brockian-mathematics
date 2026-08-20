/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header above
-- is written as a plain comment and repeated as a module docstring after the import.)

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A sequence `f : ℕ → ℤ` is a `±1` sequence if `f n ∈ {1, -1}` for every `n ≥ 1`
(the value `f 0` is irrelevant, since homogeneous arithmetic progressions only use
indices `i * d` with `i, d ≥ 1`). -/

theorem erdosDiscrepancyStatement_of_nat
    (H : ∀ f : ℕ → ℤ, IsPMOne f → ∀ C : ℕ, ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ (C : ℤ) < |hapSum f n d|) :
    ErdosDiscrepancyStatement := by
  intro f hf C
  obtain ⟨n, d, hn, hd, h⟩ := H f hf C.toNat
  refine ⟨n, d, hn, hd, lt_of_le_of_lt ?_ h⟩
  exact_mod_cast Int.self_le_toNat C

end Frontier

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

