/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Any comparison sort of 3 elements needs at least `⌈log₂ (3!)⌉ = 3` comparisons in the
worst case.

The development below is self-contained (core Lean 4 only, so that the required header
comment can be the first thing in the file, since Lean demands that `import` commands
precede every other command).

Model.  A comparison sort of three elements is modelled as a binary decision tree
(`DTree`): an internal node `cmp i j l r` compares the keys sitting at positions `i` and
`j` of the input and branches on the outcome, and a leaf `leaf q` reports the ordering
`q` it has determined.  An input is one of the `3! = 6` possible orderings of three
distinct keys (`Ord3`), `rank o i` being the rank of the key at position `i`.  The tree
sorts correctly when, on every input `o`, it reports exactly `o`.  `depth t` is the
worst-case number of comparisons the tree performs.
-/

namespace CS

/-- The `3! = 6` possible orderings of three distinct keys.  `xyz` means the key at
position `0` is the `x`-th smallest, etc. -/
inductive Ord3 where
  | abc | acb | bac | bca | cab | cba
  deriving DecidableEq, Repr

/-- `rank o i` is the rank (`0`, `1` or `2`) of the key sitting at position `i` when the
input ordering is `o`. -/

theorem sorting_ub_3 : (∀ o : Ord3, run sortTree3 o = o) ∧ depth sortTree3 = 3 := by
  refine ⟨fun o => ?_, rfl⟩
  cases o <;> rfl

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

