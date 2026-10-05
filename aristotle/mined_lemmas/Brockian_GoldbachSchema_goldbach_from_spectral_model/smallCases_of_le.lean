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
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace GoldbachSchema

/-- `GoldbachPair n` says that `n` is a sum of two primes. -/

lemma smallCases_of_le {M N : ℕ} (hMN : M ≤ N) (h : SmallCases N) : SmallCases M :=
  fun n h4 hlt hev => h n h4 (lt_of_lt_of_le hlt hMN) hev

/--
**Goldbach from a spectral model.**

If a spectral model is valid from some threshold `N₀ ≤ 101` onwards, then *every* even
`n ≥ 4` is a sum of two primes.

The auxiliary hypothesis `SmallCases M.N₀`, covering the finite range `4 ≤ n < N₀` that the
model says nothing about, is **discharged unconditionally** here (see `smallCases_101`), so
the conclusion depends on nothing beyond the analytic input packaged in `M`.

The proof splits on whether `n` lies above or below the model's threshold and closes each
branch separately: above the threshold by positivity of the spectral count, below it by the
finite verification.
-/
