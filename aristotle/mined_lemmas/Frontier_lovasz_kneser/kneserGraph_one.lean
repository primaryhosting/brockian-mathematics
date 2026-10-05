import Mathlib

/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

namespace Frontier

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are disjoint. -/

theorem kneserGraph_one (n : ℕ) : kneserGraph n 1 = (⊤ : SimpleGraph (KneserVertex n 1)) := by
  ext s t
  simp only [kneserGraph_adj, SimpleGraph.top_adj]
  constructor
  · rintro ⟨h1, -⟩
    exact fun h => h1 (congrArg Subtype.val h)
  · intro h
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp s.2
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp t.2
    have hne : a ≠ b := by
      rintro rfl
      exact h (Subtype.ext (ha.trans hb.symm))
    rw [ha, hb]
    exact ⟨by simpa using hne, by simpa using hne⟩

/-- Chromatic number of `KG_{n,1}` (the complete graph `K_n`). -/
