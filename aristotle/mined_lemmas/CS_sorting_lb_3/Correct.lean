/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
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

/-- A comparison-based sorting algorithm on `n` elements, modelled as a binary decision
tree.  A `node i j l r` compares the input values at positions `i` and `j` and branches
accordingly; a `leaf σ` outputs the permutation `σ`. -/
inductive DecTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → DecTree n
  | node : Fin n → Fin n → DecTree n → DecTree n → DecTree n

namespace DecTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed by the algorithm, i.e. the height of the
decision tree. -/

def Correct {n : ℕ} (t : DecTree n) : Prop := ∀ τ : Equiv.Perm (Fin n), t.run τ = τ

/-- A correct comparison sort on `n` elements must be able to output all `n!` permutations,
hence has at least `n!` leaves. -/
