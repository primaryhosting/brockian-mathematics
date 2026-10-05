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
