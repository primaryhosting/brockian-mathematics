/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace PCA
namespace Isolation

/-- Propositional constraint language used by the isolation engine's model. -/
inductive Formula (α : Type u) : Type u
  | var : α → Formula α
  | tru : Formula α
  | fls : Formula α
  | neg : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α
  | impl : Formula α → Formula α → Formula α

namespace Formula

/-- Semantics of a formula relative to a valuation of the atoms. -/

@[simp] theorem eval_impl {α : Type u} (v : α → Prop) (p q : Formula α) :
    eval v (.impl p q) = (eval v p → eval v q) := rfl

end Formula

/-- A proof obligation of the isolation engine: a list of assumptions together with a goal. -/
structure Obligation (α : Type u) : Type u where
  /-- The assumptions (isolation context) under which the goal must hold. -/
  hyps : List (Formula α)
  /-- The formula to be established. -/
  goal : Formula α

namespace Obligation

/-- Semantics of an obligation: under every valuation satisfying all assumptions,
the goal holds. -/
