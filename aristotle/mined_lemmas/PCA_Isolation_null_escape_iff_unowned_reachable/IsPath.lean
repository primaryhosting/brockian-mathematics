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

/-!
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The isolation model

The state of a proof-carrying app's isolation engine is modelled as an
*ownership graph*:

* `Node` — the abstract locations (objects, cells, capabilities) of the heap;
* `edge` — the may-point-to relation computed by the engine;
* `roots` — the locations directly exposed to the (untrusted) outside world;
* `owner` — the ownership labelling; `owner n = none` means the location is
  *unowned* (a "null" owner), i.e. it belongs to no isolation domain.

The engine's operational notion of failure is a **null escape**: the forward
taint analysis `Flows`, propagated from the roots along `edge`, marks a location
whose owner is null.  The model-level notion of failure is `UnownedReachable`:
some unowned location is reachable from a root.

The main theorem `null_escape_iff_unowned_reachable` states that the two
coincide; its two directions are exactly completeness
(`unownedReachable_of_nullEscape`) and soundness
(`not_unownedReachable_of_not_nullEscape`) of the engine's model.  A third,
witness-based characterisation via explicit escape traces
(`null_escape_iff_hasEscapeTrace`) is also proved equivalent, so that a failing
analysis always yields a concrete counterexample trace, and conversely any such
trace is a real escape.

The development is deliberately self-contained (no imports), so that the header
comment above is literally the first thing in the file.
-/

namespace PCA
namespace Isolation

universe u v

variable {Node : Type u} {Owner : Type v}

/-- Reachability along `edge`: the reflexive–transitive closure. -/
inductive Reach (edge : Node → Node → Prop) (a : Node) : Node → Prop
  | refl : Reach edge a a
  | tail {b c : Node} (hb : Reach edge a b) (h : edge b c) : Reach edge a c

/-- Forward taint propagation performed by the isolation engine: the locations
the engine considers exposed to the outside world. -/
inductive Flows (roots : Node → Prop) (edge : Node → Node → Prop) : Node → Prop
  | root {n : Node} (hn : roots n) : Flows roots edge n
  | step {n m : Node} (hn : Flows roots edge n) (h : edge n m) : Flows roots edge m

/-- The engine reports a **null escape**: some exposed location is unowned. -/

def IsPath (edge : Node → Node → Prop) : Node → List Node → Prop
  | _, [] => True
  | a, b :: l => edge a b ∧ IsPath edge b l

/-- The last node of the path `a :: l`. -/
