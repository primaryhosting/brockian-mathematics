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

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open SimpleGraph Finset

/-- `Arrows N s t` says that every simple graph on at least `N` vertices contains
either a clique of size `s` or an independent set of size `t`
(i.e. `N → (s, t)` in the arrow notation for Ramsey numbers). -/

lemma arrows_of_card_eq {N s t : ℕ}
    (h : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = N → G.CliqueFree s → Gᶜ.CliqueFree t → False) :
    Arrows N s t := by
  rintro V _ G hcard ⟨h1, h2⟩
  classical
  obtain ⟨A, -, hA⟩ :=
    Finset.exists_subset_card_eq (s := (univ : Finset V)) (n := N) (by simpa using hcard)
  exact h ↥(↑A : Set V) (SimpleGraph.induce (↑A : Set V) G) (by simp [hA])
    (cliqueFree_induce _ h1) (by rw [induce_compl]; exact cliqueFree_induce _ h2)

/-! ### Base cases -/

/-- `R(2, t) ≤ t`. -/
