import Brockian.GoldbachSchema

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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian
namespace GoldbachSchema

/-- The Goldbach property: `n` is a sum of two primes. -/

theorem model_exists (N : ℕ) : Nonempty (Model N) := by
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max (N + 1) 5)
  have h5 : 5 ≤ p := le_trans (le_max_right _ _) hple
  have hN : N + 1 ≤ p := le_trans (le_max_left _ _) hple
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  refine ⟨{ n := p + 3, p := p, q := 3, lt := by omega, even := hpodd.add_odd (by decide),
            hp := hp, hq := by norm_num, hp_odd := hpodd, hq_odd := by decide,
            hne := by omega, hsum := rfl }⟩

/-- **Goldbach beyond every scale.**

Originally stated relative to the named hypothesis `hmodel : ∀ N, Nonempty (Model N)`,
this is now unconditional: that hypothesis is discharged by `model_exists`.

For every bound `N` there is an even number `n > N` which is the sum of two distinct
odd primes.  (The full Goldbach conjecture — *every* even `n ≥ 4` is such a sum — remains
open; this is the unbounded-witness form of the schema.) -/
