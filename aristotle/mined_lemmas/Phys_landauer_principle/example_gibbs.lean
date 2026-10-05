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
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module doc-comment, so the header
-- above is repeated as the module documentation just after the import.)
import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Shannon entropy of a finite distribution (in nats) -/

/-- Shannon entropy (in nats) of a distribution `p` on a finite type,
using the standard convention `0 * log 0 = 0`. -/

lemma example_gibbs (r : Fin 4) :
    gibbs 1 exampleEnergy r = if r = 0 then 9 / 10 else 1 / 30 := by
  fin_cases r <;>
    (simp only [gibbs, example_partition]; simp [exampleEnergy, exp_neg_log27] <;> norm_num)

/-- **Non-vacuity of `landauer_principle`.**  There is an explicit one-bit erasure process
(with `k = T = 1`) satisfying all the hypotheses of `landauer_principle`; its dissipated heat
is `13/20 * log 27 ≈ 2.14`, which indeed exceeds `k T log 2 ≈ 0.69`. -/
