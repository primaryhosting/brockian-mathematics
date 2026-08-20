/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset SimpleGraph

/-- The Ramsey property `R(3,4) ≤ n`: every simple graph on `n` vertices contains either a
triangle or an independent set of size `4`. -/

theorem not_ramseyProp34_of_le_eight {n : ℕ} (hn : n ≤ 8) : ¬ RamseyProp34 n := by
  classical
  intro h
  set f : Fin n ↪ Fin 8 :=
    ⟨fun i => ⟨(i : ℕ), lt_of_lt_of_le i.isLt hn⟩, by
      intro a b hab
      simpa [Fin.ext_iff] using hab⟩ with hf
  have h1 : (wagner.comap f).CliqueFree 3 :=
    wagner_cliqueFree3.comap (SimpleGraph.Embedding.comap f wagner)
  have h2 : (wagner.comap f)ᶜ.CliqueFree 4 := by
    rw [compl_comap]
    exact wagner_compl_cliqueFree4.comap (SimpleGraph.Embedding.comap f wagnerᶜ)
  rcases h (wagner.comap f) with ⟨s, hs⟩ | ⟨t, ht⟩
  · exact h1 s hs
  · exact h2 t (by rwa [SimpleGraph.isNClique_compl])

/-! ### The Ramsey number `R(3,4) = 9` -/

/-- `R(3,4) = 9`: nine is the least `n` such that every graph on `n` vertices contains a
triangle or an independent set of size four. -/
