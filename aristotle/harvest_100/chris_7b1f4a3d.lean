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
def Guard.eval {α : Type u} (env : α → Bool) : Guard α → Bool
  | .atom a => env a
  | .tru => true
  | .fls => false
  | .neg g => !(g.eval env)
  | .conj g₁ g₂ => (g₁.eval env) && (g₂.eval env)
  | .disj g₁ g₂ => (g₁.eval env) || (g₂.eval env)

/-- An isolation rule: a guard together with the action (isolation verdict) it triggers. -/
structure Rule (α : Type u) (β : Type v) where
  guard : Guard α
  action : β

/-- Split a guard along its top-level disjunctions into the list of disjuncts. -/
def splitGuard {α : Type u} : Guard α → List (Guard α)
  | .disj g₁ g₂ => splitGuard g₁ ++ splitGuard g₂
  | g => [g]

/-- The disjunct list of a guard is never empty. -/
theorem splitGuard_ne_nil {α : Type u} (g : Guard α) : splitGuard g ≠ [] := by
  induction g with
  | disj g₁ g₂ ih₁ _ =>
      simp only [splitGuard, ne_eq, List.append_eq_nil_iff, not_and]
      intro h
      exact absurd h ih₁
  | _ => simp [splitGuard]

/-- Splitting a guard is semantics preserving: the guard holds iff some disjunct holds. -/
theorem any_splitGuard_eval {α : Type u} (env : α → Bool) (g : Guard α) :
    ((splitGuard g).any (fun h => h.eval env)) = g.eval env := by
  induction g with
  | disj g₁ g₂ ih₁ ih₂ =>
      simp [splitGuard, Guard.eval, List.any_append, ih₁, ih₂]
  | _ => simp [splitGuard]

/-- Split a single rule into the rules obtained from its top-level disjuncts,
keeping the same action. -/
def splitRule {α : Type u} {β : Type v} (r : Rule α β) : List (Rule α β) :=
  (splitGuard r.guard).map (fun g => ⟨g, r.action⟩)

/-- Split every rule of a policy. -/
def splitRules {α : Type u} {β : Type v} : List (Rule α β) → List (Rule α β)
  | [] => []
  | r :: rs => splitRule r ++ splitRules rs

/-- First-match semantics of a policy: the action of the first rule whose guard holds. -/
def firstMatch {α : Type u} {β : Type v} (env : α → Bool) : List (Rule α β) → Option β
  | [] => none
  | r :: rs => if r.guard.eval env then some r.action else firstMatch env rs

/-- The list of actions enabled by a policy under a given environment. -/
def enabled {α : Type u} {β : Type v} (env : α → Bool) (rs : List (Rule α β)) : List β :=
  (rs.filter (fun r => r.guard.eval env)).map Rule.action

theorem firstMatch_append {α : Type u} {β : Type v} (env : α → Bool)
    (l₁ l₂ : List (Rule α β)) :
    firstMatch env (l₁ ++ l₂) = (firstMatch env l₁).or (firstMatch env l₂) := by
  induction l₁ with
  | nil => simp [firstMatch]
  | cons r rs ih =>
      by_cases h : r.guard.eval env
      · simp [firstMatch, h]
      · simp [firstMatch, h, ih]

/-- Evaluating the split of a single rule: it matches exactly when the original rule
matches, with the same action. -/
theorem firstMatch_splitRule {α : Type u} {β : Type v} (env : α → Bool) (r : Rule α β) :
    firstMatch env (splitRule r) = if r.guard.eval env then some r.action else none := by
  obtain ⟨g, a⟩ := r
  simp only [splitRule]
  induction g with
  | disj g₁ g₂ ih₁ ih₂ =>
      simp only [splitGuard, List.map_append, firstMatch_append, ih₁, ih₂, Guard.eval]
      by_cases h₁ : Guard.eval env g₁ <;> by_cases h₂ : Guard.eval env g₂ <;>
        simp [h₁, h₂]
  | _ => simp [splitGuard, firstMatch]

/-- **Disjunction split preserves semantics.**  Rewriting every rule of an isolation
policy into the rules given by its top-level disjuncts (all carrying the original
action) yields a policy with exactly the same first-match behaviour, in every
environment. -/
theorem disjunction_split_preserves_semantics {α : Type u} {β : Type v} (env : α → Bool)
    (rs : List (Rule α β)) :
    firstMatch env (splitRules rs) = firstMatch env rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      rw [splitRules, firstMatch_append, firstMatch_splitRule, ih]
      by_cases h : r.guard.eval env <;> simp [firstMatch, h]

/-- Membership in the enabled-action list. -/
theorem mem_enabled {α : Type u} {β : Type v} (env : α → Bool) (rs : List (Rule α β))
    (b : β) :
    b ∈ enabled env rs ↔ ∃ r ∈ rs, r.guard.eval env = true ∧ b = r.action := by
  simp only [enabled, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨r, ⟨hr, hev⟩, rfl⟩
    exact ⟨r, hr, hev, rfl⟩
  · rintro ⟨r, hr, hev, rfl⟩
    exact ⟨r, ⟨hr, hev⟩, rfl⟩

/-- Splitting one rule preserves the actions it enables. -/
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

