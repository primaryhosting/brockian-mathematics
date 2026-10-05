/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace Isolation

universe u

/-- Syntax of isolation policies over an atom type `α`. -/
inductive Policy (α : Type u) : Type u
  | atom : α → Policy α
  | tru : Policy α
  | fls : Policy α
  | neg : Policy α → Policy α
  | conj : Policy α → Policy α → Policy α
  | disj : Policy α → Policy α → Policy α

namespace Policy

variable {α : Type u}

/-- Semantics of a policy relative to a valuation of atoms. -/

theorem split_disjFree (p : Policy α) :
    ∀ b ∈ Policy.split p, Policy.DisjFree b := by
  induction p with
  | atom a => intro b hb; simp [Policy.split] at hb; subst hb; trivial
  | tru => intro b hb; simp [Policy.split] at hb; subst hb; trivial
  | fls => intro b hb; simp [Policy.split] at hb; subst hb; trivial
  | neg p _ => intro b hb; simp [Policy.split] at hb; subst hb; trivial
  | conj p q ihp ihq =>
      intro b hb
      simp only [Policy.split, List.mem_flatMap, List.mem_map] at hb
      obtain ⟨x, hx, y, hy, rfl⟩ := hb
      exact ⟨ihp x hx, ihq y hy⟩
  | disj p q ihp ihq =>
      intro b hb
      simp only [Policy.split, List.mem_append] at hb
      rcases hb with h | h
      · exact ihp b h
      · exact ihq b h

/-- The split is never empty: the engine always produces at least one branch. -/
