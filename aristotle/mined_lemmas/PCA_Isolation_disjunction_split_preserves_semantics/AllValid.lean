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

def AllValid {α : Type u} (os : List (Obligation α)) : Prop := ∀ o ∈ os, Valid o

end Obligation

/-- The disjunction split transformation: an obligation whose assumption list is
`pre ++ (p ∨ q) :: post` is replaced by the two obligations obtained by replacing the
disjunction with each disjunct in turn. -/
