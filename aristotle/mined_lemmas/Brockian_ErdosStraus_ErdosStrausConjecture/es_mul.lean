import Brockian.ErdosStraus

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

/-
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ErdosStraus

/-- `ES n` says that `4 / n` is a sum of three positive unit fractions
(the Erdős–Straus property for `n`; the denominators need not be distinct). -/

theorem es_mul {a m : ℕ} (ha : ES a) (hm : 0 < m) : ES (a * m) := by
  obtain ⟨x, y, z, hx, hy, hz, h⟩ := ha
  refine ⟨m * x, m * y, m * z, by positivity, by positivity, by positivity, ?_⟩
  push_cast
  rw [show (4 : ℚ) / ((a : ℚ) * m) = (1 / m) * (4 / a) by ring, h]
  ring

/-- `ES 2`. -/
