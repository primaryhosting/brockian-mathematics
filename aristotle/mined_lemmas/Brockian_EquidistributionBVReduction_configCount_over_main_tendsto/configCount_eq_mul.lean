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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of "configurations" below `N` for the modulus `q` and the residues `a`, `b`:
the pairs `(m, n)` with `m, n < N`, `m ≡ a [MOD q]` and `n ≡ b [MOD q]`. -/

lemma configCount_eq_mul (q a b N : ℕ) :
    configCount q a b N =
      Nat.count (fun x => x ≡ a [MOD q]) N * Nat.count (fun x => x ≡ b [MOD q]) N := by
  rw [configCount, Finset.filter_product (fun x => x ≡ a [MOD q]) (fun x => x ≡ b [MOD q]),
    Finset.card_product, Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]

/-- The one-dimensional count in an arithmetic progression differs from its main term by
at most `1`. -/
