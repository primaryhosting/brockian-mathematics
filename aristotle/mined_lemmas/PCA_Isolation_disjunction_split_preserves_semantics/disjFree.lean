/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option autoImplicit false

namespace PCA
namespace Isolation

universe u

/-- Syntax of isolation constraints over a type `α` of atomic predicates
(e.g. "capability `c` is granted", "resource `r` is reachable"). -/
inductive Constraint (α : Type u) : Type u
  | atom : α → Constraint α
  | tru : Constraint α
  | fls : Constraint α
  | neg : Constraint α → Constraint α
  | conj : Constraint α → Constraint α → Constraint α
  | disj : Constraint α → Constraint α → Constraint α
  deriving Repr

namespace Constraint

variable {α : Type u}

/-- Semantics of an isolation constraint relative to a valuation `v` of the atoms. -/

def disjFree : Constraint α → Prop
  | disj _ _ => False
  | _ => True

