/-!
# Self Nonprediction
Category: Frontier Mind
Target: Frontier.self_nonprediction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Setting

We model a family of machines by a type `M` together with two observables:

* `pred m : Bool` — the prediction machine `m` makes about its own next output,
  issued *before* the output is produced;
* `out m : Bool` — the output machine `m` actually produces.

The only structural assumption is a *self-reference* (recursion-theorem style) principle:
for every post-processing `f : Bool → Bool` there is a machine in the family whose output
is `f` applied to its own prediction.  This is exactly the ability, guaranteed by Kleene's
recursion theorem in any reasonable programming formalism, to build a machine that reads
off its own prediction and then acts on it.

The diagonal argument then shows prediction must fail somewhere: taking `f = not` yields a
machine that outputs the negation of its own forecast.  The diagonal step is the two-element
instance of Cantor's argument (`!b ≠ b`, in Mathlib `Bool.not_ne_self`); it is proved here by
`decide` so that the file has no dependencies beyond core Lean.
-/

namespace Frontier

/-- The diagonal step: a Boolean never equals its negation.
(Mathlib states this as `Bool.not_ne_self`.) -/

theorem self_reference_example :
    ∀ f : Bool → Bool, ∃ m : Bool × Bool, (fun p => p.2) m = f ((fun p => p.1) m) :=
  fun f => ⟨(true, f true), rfl⟩

/-- Instantiating the theorem on that family: some machine mispredicts itself. -/
example : ∃ m : Bool × Bool, m.1 ≠ m.2 :=
  self_nonprediction (fun p : Bool × Bool => p.1) (fun p : Bool × Bool => p.2)
    self_reference_example

end Frontier

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

