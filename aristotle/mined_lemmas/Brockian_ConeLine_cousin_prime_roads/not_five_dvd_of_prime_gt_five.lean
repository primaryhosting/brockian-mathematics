/-
# Cousin Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.cousin_prime_roads
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

namespace Brockian
namespace ConeLine

/-- If `n` is a prime greater than `5`, then `n` is not divisible by `5`. -/

theorem not_five_dvd_of_prime_gt_five {n : ℕ} (hn : Nat.Prime n) (h : 5 < n) :
    ¬ (5 ∣ n) := by
  intro hdvd
  rcases (Nat.Prime.eq_one_or_self_of_dvd hn 5 hdvd) with h1 | h2
  · omega
  · omega

/-- **Cousin prime roads.** For a cousin prime pair `(p, p + 4)` with `p > 5`, the residues
mod `5` are exactly one of `(2,1)`, `(3,2)`, `(4,3)`. -/
