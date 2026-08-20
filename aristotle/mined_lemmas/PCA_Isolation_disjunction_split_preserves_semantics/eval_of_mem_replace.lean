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

theorem eval_of_mem_replace {α : Type u} {v : α → Prop} {pre post : List (Formula α)}
    {r s : Formula α} (hs : ∀ f ∈ pre ++ s :: post, Formula.eval v f)
    (hr : Formula.eval v r) : ∀ f ∈ pre ++ r :: post, Formula.eval v f := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact hs f (List.mem_append.mpr (Or.inl hf))
  · rcases List.mem_cons.mp hf with hf | hf
    · exact hf ▸ hr
    · exact hs f (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hf)))

/-- **Disjunction split preserves semantics.**

Splitting a disjunctive assumption of a proof obligation into the two corresponding
obligations is both sound and complete: the original obligation is valid if and only if
both resulting obligations are valid. -/
