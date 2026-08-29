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

/-
Note on imports.  The header comment above is a *module docstring*, which Lean
parses as a command; consequently no `import` line may follow it.  The
development below is therefore self-contained in core Lean.  The reachability
relation `PCA.Isolation.Reaches` defined here is the reflexive-transitive
closure of the reference relation, i.e. the exact analogue of Mathlib's
`Relation.ReflTransGen`; the two directions of the main theorem correspond to
the induction principles `Relation.ReflTransGen.head_induction_on` /
`Relation.ReflTransGen.tail` there.  A Mathlib-based restatement, proved by
transporting along an equivalence with `Relation.ReflTransGen`, is given in
`RequestProject/PCA/IsolationMathlib.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

universe u v

variable {V : Type u} {D : Type v}

/-- Reflexive-transitive closure of the reference relation `edge`:
`Reaches edge a b` holds when `b` can be reached from `a` by following a finite
(possibly empty) chain of heap references. -/
inductive Reaches (edge : V → V → Prop) : V → V → Prop
  | refl (a : V) : Reaches edge a a
  | tail {a b c : V} : Reaches edge a b → edge b c → Reaches edge a c

/-- One expansion step of the isolation engine's worklist: keep everything already
discovered and add every heap node directly referenced from a discovered node. -/

def iterSet (edge : V → V → Prop) (roots : Set V) (n : Nat) : Set V :=
  {w | iter edge (· ∈ roots) n w}

/-- Set-valued reachable set, phrased with `Relation.ReflTransGen`. -/
