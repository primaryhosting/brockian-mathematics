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
set_option relaxedAutoImplicit false

namespace PCA.Isolation

universe u

/-- Conditions of the isolation engine's policy language over an atom type `α`. -/
inductive Cond (α : Type u) : Type u
  | tt : Cond α
  | ff : Cond α
  | atom : α → Cond α
  | not : Cond α → Cond α
  | and : Cond α → Cond α → Cond α
  | or : Cond α → Cond α → Cond α

/-- Boolean semantics of a condition relative to a valuation `σ` of the atoms. -/
def Cond.eval {α : Type u} (σ : α → Bool) : Cond α → Bool
  | .tt => true
  | .ff => false
  | .atom a => σ a
  | .not c => !(c.eval σ)
  | .and c₁ c₂ => (c₁.eval σ) && (c₂.eval σ)
  | .or c₁ c₂ => (c₁.eval σ) || (c₂.eval σ)

/-- The effect attached to a rule: the request is either permitted or blocked. -/
inductive Effect : Type
  | allow : Effect
  | deny : Effect
  deriving Repr, DecidableEq

/-- A single isolation rule: a guard condition together with an effect. -/
structure Rule (α : Type u) : Type u where
  cond : Cond α
  effect : Effect

/-- An isolation policy is an ordered list of rules (first match wins). -/
abbrev Policy (α : Type u) : Type u := List (Rule α)

/-- First-match-wins decision procedure. `none` means "no rule applies". -/
def evalPolicy {α : Type u} (σ : α → Bool) : Policy α → Option Effect
  | [] => none
  | r :: rest => if r.cond.eval σ then some r.effect else evalPolicy σ rest

/-- A policy permits a request when the first matching rule allows it
(default: deny). -/
def permits {α : Type u} (σ : α → Bool) (p : Policy α) : Bool :=
  evalPolicy σ p == some Effect.allow

/-- Top-level disjunctive splitting of a condition: the list of its
top-level disjuncts. -/
def Cond.disjuncts {α : Type u} : Cond α → List (Cond α)
  | .or c₁ c₂ => c₁.disjuncts ++ c₂.disjuncts
  | c => [c]

/-- Splitting a rule replaces it by one rule per top-level disjunct of its
guard, all carrying the original effect. -/
def splitRule {α : Type u} (r : Rule α) : Policy α :=
  r.cond.disjuncts.map fun c => ⟨c, r.effect⟩

/-- The isolation engine's disjunction-split transformation on policies. -/
def splitPolicy {α : Type u} (p : Policy α) : Policy α :=
  p.flatMap splitRule

/-- A condition holds iff one of its top-level disjuncts holds. -/
theorem Cond.eval_eq_any_disjuncts {α : Type u} (σ : α → Bool) (c : Cond α) :
    c.eval σ = c.disjuncts.any (fun d => d.eval σ) := by
  induction c with
  | tt => simp [Cond.eval, Cond.disjuncts]
  | ff => simp [Cond.eval, Cond.disjuncts]
  | atom a => simp [Cond.eval, Cond.disjuncts]
  | not c _ => simp [Cond.eval, Cond.disjuncts]
  | and c₁ c₂ _ _ => simp [Cond.eval, Cond.disjuncts]
  | or c₁ c₂ ih₁ ih₂ =>
      simp [Cond.eval, Cond.disjuncts, List.any_append, ih₁, ih₂]

/-- Decision semantics of a block of rules sharing one effect, prepended to a
remaining policy. -/
theorem evalPolicy_map_append {α : Type u} (σ : α → Bool) (ds : List (Cond α))
    (e : Effect) (rest : Policy α) :
    evalPolicy σ ((ds.map fun c => (⟨c, e⟩ : Rule α)) ++ rest) =
      if ds.any (fun d => d.eval σ) then some e else evalPolicy σ rest := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      by_cases hd : d.eval σ
      · simp [evalPolicy, hd]
      · simp [evalPolicy, hd, ih]

/-- **Main theorem.** The disjunction-split transformation of the isolation
engine preserves the first-match-wins decision semantics of every policy,
for every valuation of the atoms. -/
theorem disjunction_split_preserves_semantics {α : Type u} (σ : α → Bool)
    (p : Policy α) : evalPolicy σ (splitPolicy p) = evalPolicy σ p := by
  induction p with
  | nil => simp [splitPolicy, evalPolicy]
  | cons r rest ih =>
      have h : evalPolicy σ (splitPolicy (r :: rest)) =
          if r.cond.disjuncts.any (fun d => d.eval σ) then some r.effect
          else evalPolicy σ (splitPolicy rest) := by
        simpa [splitPolicy, splitRule, List.flatMap_cons] using
          evalPolicy_map_append σ r.cond.disjuncts r.effect (splitPolicy rest)
      rw [h, ih, ← Cond.eval_eq_any_disjuncts]
      by_cases hc : r.cond.eval σ <;> simp [evalPolicy, hc]

/-- Soundness: anything permitted by the split policy was permitted before. -/
theorem split_sound {α : Type u} (σ : α → Bool) (p : Policy α)
    (h : permits σ (splitPolicy p) = true) : permits σ p = true := by
  rwa [permits, disjunction_split_preserves_semantics] at h

/-- Completeness: anything permitted before is permitted by the split policy. -/
theorem split_complete {α : Type u} (σ : α → Bool) (p : Policy α)
    (h : permits σ p = true) : permits σ (splitPolicy p) = true := by
  rwa [permits, disjunction_split_preserves_semantics]

/-- Sanity check: the transformation genuinely splits a disjunctive rule
into two rules. -/
example :
    (splitPolicy [⟨Cond.or (Cond.atom 0) (Cond.atom 1), Effect.allow⟩] : Policy Nat).length
      = 2 := rfl

end PCA.Isolation

#print axioms PCA.Isolation.disjunction_split_preserves_semantics
#print axioms PCA.Isolation.split_sound
#print axioms PCA.Isolation.split_complete

