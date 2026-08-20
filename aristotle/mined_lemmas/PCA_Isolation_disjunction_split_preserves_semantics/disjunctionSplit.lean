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

def disjunctionSplit {α : Type u} (pre post : List (Formula α)) (p q goal : Formula α) :
    List (Obligation α) :=
  [⟨pre ++ p :: post, goal⟩, ⟨pre ++ q :: post, goal⟩]

/-- Assumptions in `pre ++ r :: post` are available whenever every member of that list
is satisfied: the auxiliary transfer lemma used by the split. -/
