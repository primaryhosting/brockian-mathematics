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

import Mathlib

/-!
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Weyl.WeylLawTarget

open Filter

/-- The eigenvalue counting function of a sequence `lam : ℕ → ℝ` of eigenvalues
(listed with multiplicity): `counting lam t` is the number of indices `n` with
`lam n ≤ t`. -/

theorem counting_mono (lam : ℕ → ℝ) (hfin : ∀ t : ℝ, {n : ℕ | lam n ≤ t}.Finite) :
    Monotone (counting lam) := by
  intro s t hst
  exact Set.ncard_le_ncard (fun n hn => le_trans hn hst) (hfin t)

/-- For every `N` there is a spectral parameter at which at least `N` eigenvalues
have been counted: the sublevel set at `t = max_{n < N} lam n` contains `Finset.range N`.
This is the existence statement that the main theorem used to assume. -/
