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

theorem split_ne_nil (c : Cond S) : split c ≠ [] := by
  induction c with
  | or c₁ c₂ ih₁ _ =>
      simp only [split_or, ne_eq, List.append_eq_nil_iff, not_and]
      exact fun h => absurd h ih₁
  | _ => simp [split]

/-- **Disjunction split preserves semantics.**

Splitting an isolation condition along its top-level disjunctions is both sound and
complete for the semantics: a state satisfies the original condition exactly when it
satisfies at least one of the branches produced by the split.

The inductive step is the distribution of an existential over a list append, which is
`List.mem_append` combined with `or_and_right` and `exists_or`. -/
