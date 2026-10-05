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
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u v

namespace PCA
namespace Isolation

/-- Guards of the isolation engine's policy language: boolean combinations of
atomic predicates over an environment. -/
inductive Guard (α : Type u) : Type _
  | atom : α → Guard α
  | tru : Guard α
  | fls : Guard α
  | neg : Guard α → Guard α
  | conj : Guard α → Guard α → Guard α
  | disj : Guard α → Guard α → Guard α

/-- Semantics of a guard relative to an environment assigning truth values to atoms. -/

theorem mem_enabled_splitRules {α : Type u} {β : Type v} (env : α → Bool)
    (rs : List (Rule α β)) (b : β) :
    b ∈ enabled env (splitRules rs) ↔ b ∈ enabled env rs := by
  have happ : ∀ l₁ l₂ : List (Rule α β),
      enabled env (l₁ ++ l₂) = enabled env l₁ ++ enabled env l₂ := by
    intro l₁ l₂
    simp [enabled, List.filter_append]
  induction rs with
  | nil => simp [splitRules, enabled]
  | cons r rs ih =>
      rw [splitRules, happ, List.mem_append, mem_enabled_splitRule env r b]
      simp only [ih, mem_enabled]
      constructor
      · rintro (⟨hev, rfl⟩ | ⟨r', hr', hev, rfl⟩)
        · exact ⟨r, List.mem_cons_self .., hev, rfl⟩
        · exact ⟨r', List.mem_cons_of_mem _ hr', hev, rfl⟩
      · rintro ⟨r', hr', hev, rfl⟩
        rcases List.mem_cons.mp hr' with rfl | hr'
        · exact Or.inl ⟨hev, rfl⟩
        · exact Or.inr ⟨r', hr', hev, rfl⟩

/-- Sanity check: the split of a rule with a disjunctive guard really does produce
two rules carrying the original action. -/
example :
    splitRules [({ guard := .disj (.atom 0) (.atom 1), action := true } : Rule Nat Bool)] =
      [⟨.atom 0, true⟩, ⟨.atom 1, true⟩] := rfl

end Isolation
end PCA

