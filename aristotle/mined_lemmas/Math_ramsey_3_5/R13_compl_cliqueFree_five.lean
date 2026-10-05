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

lemma R13_compl_cliqueFree_five : R13ᶜ.CliqueFree 5 := by
  intro T hT
  set f := T.orderIsoOfFin hT.2
  have hmem : ∀ i : Fin 5, ((f i : Fin 13)) ∈ T := fun i => (f i).2
  have hmono : ∀ i j : Fin 5, i < j → ((f i : Fin 13) : ℕ) < ((f j : Fin 13) : ℕ) :=
    fun i j hij => (OrderIso.lt_iff_lt f).mpr hij
  have hnadj : ∀ i j : Fin 5, i ≠ j → ¬ R13Adj (f i : Fin 13) (f j : Fin 13) := by
    intro i j hij
    have hne : ((f i : Fin 13)) ≠ ((f j : Fin 13)) := by
      intro h
      exact hij (f.injective (Subtype.ext h))
    exact (hT.1 (hmem i) (hmem j) hne).2
  have h := no_indep5 ((f 4 : Fin 13) : ℕ) (f 4 : Fin 13).2
    ((f 3 : Fin 13) : ℕ) (hmono 3 4 (by decide))
    ((f 2 : Fin 13) : ℕ) (hmono 2 3 (by decide))
    ((f 1 : Fin 13) : ℕ) (hmono 1 2 (by decide))
    ((f 0 : Fin 13) : ℕ) (hmono 0 1 (by decide))
  rcases h with h|h|h|h|h|h|h|h|h|h
  · exact hnadj 0 1 (by decide) h
  · exact hnadj 0 2 (by decide) h
  · exact hnadj 0 3 (by decide) h
  · exact hnadj 0 4 (by decide) h
  · exact hnadj 1 2 (by decide) h
  · exact hnadj 1 3 (by decide) h
  · exact hnadj 1 4 (by decide) h
  · exact hnadj 2 3 (by decide) h
  · exact hnadj 2 4 (by decide) h
  · exact hnadj 3 4 (by decide) h

/-! ### The Ramsey number `R(3,5) = 14` -/

/-- **`R(3,5) = 14`**: `14` is the least `N` such that every graph on at least `N`
vertices contains a triangle or an independent set of size `5`. -/
