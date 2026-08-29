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
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean 4 requires `import` to precede every command, including module docstrings,
so the required header is reproduced verbatim as a module docstring just below
the import as well.)
-/

import Mathlib

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian
namespace GoldbachComb

/-! ## Averages and covariance over a finite sample -/

/-- The empirical mean of `f` over a finite set `S` of naturals. -/

noncomputable def goldbachIndicator (n : ℕ) : ℝ := if IsGoldbach n then 1 else 0

/-- Indicator of the Goldbach exceptions (numbers that are *not* sums of two primes). -/
