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

theorem mem_enabled_splitRule {α : Type u} {β : Type v} (env : α → Bool) (r : Rule α β)
    (b : β) :
    b ∈ enabled env (splitRule r) ↔ (r.guard.eval env = true ∧ b = r.action) := by
  rw [mem_enabled]
  constructor
  · rintro ⟨r', hr', hev, rfl⟩
    simp only [splitRule, List.mem_map] at hr'
    obtain ⟨g, hg, rfl⟩ := hr'
    refine ⟨?_, rfl⟩
    rw [← any_splitGuard_eval env r.guard]
    simp only [List.any_eq_true]
    exact ⟨g, hg, hev⟩
  · rintro ⟨hg, rfl⟩
    have hany := any_splitGuard_eval env r.guard
    rw [hg] at hany
    simp only [List.any_eq_true] at hany
    obtain ⟨g, hgmem, hgev⟩ := hany
    refine ⟨⟨g, r.action⟩, ?_, hgev, rfl⟩
    simp only [splitRule, List.mem_map]
    exact ⟨g, hgmem, rfl⟩

/-- The split also preserves the (unordered) set of enabled actions. -/
