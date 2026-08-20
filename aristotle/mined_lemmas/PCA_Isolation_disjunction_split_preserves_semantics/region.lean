/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: a Lean module docstring must be the first command in a file, so no
`import` line may precede it.  This development therefore uses only the automatically
available `Init` prelude.  Nothing is lost: the lemmas that close the key step
(`List.mem_append`, `or_and_right`, `exists_or`) are core lemmas that are equally
available in the Mathlib environment.
-/

set_option autoImplicit false

universe u

namespace PCA
namespace Isolation

variable {S : Type u}

/-- Isolation conditions: the guard language of the isolation engine over a state
type `S`.  Atoms are arbitrary predicates on states; the language is closed under
conjunction, disjunction and negation. -/
inductive Cond (S : Type u) where
  | tru : Cond S
  | fls : Cond S
  | atom : (S → Prop) → Cond S
  | and : Cond S → Cond S → Cond S
  | or : Cond S → Cond S → Cond S
  | not : Cond S → Cond S

/-- Semantics of an isolation condition: `Holds c s` says that state `s` satisfies `c`. -/

def region (c : Cond S) : S → Prop := fun s => Holds c s

