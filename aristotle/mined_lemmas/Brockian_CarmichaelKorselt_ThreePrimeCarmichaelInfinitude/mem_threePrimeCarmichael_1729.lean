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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` which is a Fermat pseudoprime to every base,
i.e. `a ^ n ≡ a [MOD n]` for all `a`. -/

theorem mem_threePrimeCarmichael_1729 : 1729 ∈ ThreePrimeCarmichael := by
  have h : (1729 : ℕ) = (6 * 1 + 1) * (12 * 1 + 1) * (18 * 1 + 1) := by norm_num
  have h6 : Nat.Prime (6 * 1 + 1) := by norm_num
  have h12 : Nat.Prime (12 * 1 + 1) := by norm_num
  have h18 : Nat.Prime (18 * 1 + 1) := by norm_num
  refine ⟨h ▸ isCarmichael_chernick le_rfl h6 h12 h18, 7, 13, 19, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num

end CarmichaelKorselt
end Brockian

