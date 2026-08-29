/-!
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-- A set of privileges, represented by its membership predicate. -/
def PrivSet (α : Type _) : Type _ := α → Prop

namespace PrivSet

variable {α : Type _}

instance : Membership α (PrivSet α) := ⟨fun S a => S a⟩

instance : HasSubset (PrivSet α) := ⟨fun S T => ∀ ⦃a⦄, a ∈ S → a ∈ T⟩

/-- Adding one privilege to a privilege set. -/
def insert (a : α) (S : PrivSet α) : PrivSet α := fun b => b = a ∨ b ∈ S

@[simp] theorem mem_insert_iff {a b : α} {S : PrivSet α} :
    b ∈ insert a S ↔ b = a ∨ b ∈ S := Iff.rfl

theorem Subset.rfl {S : PrivSet α} : S ⊆ S := fun _ h => h

theorem Subset.trans {S T U : PrivSet α} (h₁ : S ⊆ T) (h₂ : T ⊆ U) : S ⊆ U :=
  fun _ h => h₂ (h₁ h)

theorem insert_subset_insert {a : α} {S T : PrivSet α} (h : S ⊆ T) :
    insert a S ⊆ insert a T := by
  rintro b (rfl | hb)
  · exact Or.inl rfl
  · exact Or.inr (h hb)

end PrivSet

/-- A privilege-granting rule of the isolation engine: an app that already holds every
privilege in `guard` may additionally acquire the privilege `target`. -/
structure Rule (α : Type _) where
  /-- Privileges that must already be held for the rule to fire. -/
  guard : PrivSet α
  /-- Privilege granted when the rule fires. -/
  target : α

/-- A rule set (policy) of the isolation engine. -/
def Policy (α : Type _) : Type _ := Rule α → Prop

instance {α : Type _} : Membership (Rule α) (Policy α) := ⟨fun R r => R r⟩

instance {α : Type _} : HasSubset (Policy α) := ⟨fun R₁ R₂ => ∀ ⦃r⦄, r ∈ R₁ → r ∈ R₂⟩

/-- `Reach R S₀ S` : the privilege set `S` is reachable from the initial privilege set
`S₀` by repeatedly firing rules of the policy `R`. -/
inductive Reach {α : Type _} (R : Policy α) (S₀ : PrivSet α) : PrivSet α → Prop
  | init : Reach R S₀ S₀
  | step {S : PrivSet α} {r : Rule α} :
      Reach R S₀ S → r ∈ R → r.guard ⊆ S → Reach R S₀ (PrivSet.insert r.target S)

/-- The isolation engine's escape predicate: starting from the privileges `S₀` and using
the policy `R`, the app can reach a state in which it holds the privilege `p`. -/
def Escapes {α : Type _} (R : Policy α) (S₀ : PrivSet α) (p : α) : Prop :=
  ∃ S, Reach R S₀ S ∧ p ∈ S

/-- Simulation lemma: enlarging the policy and the initial privileges can only enlarge
the reachable privilege sets. -/
theorem reach_mono {α : Type _} {R₁ R₂ : Policy α} {S₀ T₀ : PrivSet α}
    (hR : R₁ ⊆ R₂) (hS : S₀ ⊆ T₀) {S : PrivSet α} (h : Reach R₁ S₀ S) :
    ∃ T, Reach R₂ T₀ T ∧ S ⊆ T := by
  induction h with
  | init => exact ⟨T₀, Reach.init, hS⟩
  | @step S r _ hr hg ih =>
      obtain ⟨T, hT, hST⟩ := ih
      exact ⟨PrivSet.insert r.target T, Reach.step hT (hR hr) (PrivSet.Subset.trans hg hST),
        PrivSet.insert_subset_insert hST⟩

/-- **Privilege-escape monotonicity.** If the isolation engine's policy is relaxed
(every rule of `R₁` is also a rule of `R₂`) and the app starts with at least as many
privileges, then every privilege escape possible before is still possible. -/
theorem priv_escape_monotone {α : Type _} {R₁ R₂ : Policy α} {S₀ T₀ : PrivSet α} {p : α}
    (hR : R₁ ⊆ R₂) (hS : S₀ ⊆ T₀) (h : Escapes R₁ S₀ p) : Escapes R₂ T₀ p := by
  obtain ⟨S, hS', hp⟩ := h
  obtain ⟨T, hT, hST⟩ := reach_mono hR hS hS'
  exact ⟨T, hT, hST hp⟩

/-- Contrapositive (safety) form: if the more permissive configuration admits no escape
to `p`, then neither does the more restrictive one. -/
theorem not_escapes_of_not_escapes {α : Type _} {R₁ R₂ : Policy α} {S₀ T₀ : PrivSet α}
    {p : α} (hR : R₁ ⊆ R₂) (hS : S₀ ⊆ T₀) (h : ¬ Escapes R₂ T₀ p) : ¬ Escapes R₁ S₀ p :=
  fun hesc => h (priv_escape_monotone hR hS hesc)

/-- Sanity check that the escape predicate is not vacuous: with the single rule
"holding privilege `0` grants privilege `1`", an app starting with privilege `0`
escapes to privilege `1`. -/
example : Escapes (α := Nat) (fun r => r = ⟨fun a => a = 0, 1⟩) (fun a => a = 0) 1 := by
  refine ⟨PrivSet.insert 1 (fun a => a = 0), ?_, Or.inl rfl⟩
  exact Reach.step (r := ⟨fun a => a = 0, 1⟩) Reach.init rfl (fun _ h => h)

end PCA.Isolation

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

