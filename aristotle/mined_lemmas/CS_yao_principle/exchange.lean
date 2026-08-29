/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is repeated as a module docstring below; Lean requires `import`
-- to precede any module docstring.)

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

variable {A I : Type*}

/-- The expected cost of the randomized algorithm given by the distribution `p` over the
(deterministic) algorithms `A`, run on the input `i`. -/

lemma exchange [Fintype A] [Fintype I] (cost : A → I → ℝ) (p : A → ℝ) (q : I → ℝ) :
    ∑ i, q i * randCost cost p i = ∑ a, p a * distCost cost a q := by
  simp only [randCost, distCost, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

end Aux

section Alternative

variable [Fintype A] [Fintype I]

/-- The theorem of the alternative underlying the minimax theorem (a form of Ville's theorem):
for any real matrix `M`, either there is a distribution `q` over the columns making all row
averages nonnegative, or there is a distribution `p` over the rows making all column averages
strictly negative. -/
