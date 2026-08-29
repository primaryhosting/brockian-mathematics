/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- A comparison-based sorting algorithm for `n` elements, modelled as a binary
decision tree.  An internal node `node i j l r` compares the inputs at positions
`i` and `j`, descending into `l` if `a i < a j` and into `r` otherwise; a leaf
`leaf p` outputs the permutation `p`. -/
inductive CompTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n
  deriving Inhabited

namespace CompTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed by the algorithm, i.e. the
height of the decision tree. -/

theorem sorting_lb_4_five (t : CompTree 4)
    (hcorrect : ∀ σ : Equiv.Perm (Fin 4), t.run σ = σ) : 5 ≤ t.depth := by
  have := sorting_lb_4 t hcorrect
  rwa [clog_two_factorial_four] at this

end CS

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

