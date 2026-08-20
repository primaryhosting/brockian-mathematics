import RequestProject.Ramsey
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
# The Ramsey number `R(4,4) = 18`

We define two-colourings of the edges of a complete graph as simple graphs (`red` = adjacent,
`blue` = non-adjacent), and prove that every graph on 18 vertices contains a red or a blue
clique on 4 vertices, while the Paley graph on 17 vertices contains neither.
-/

open Finset
open scoped Classical

namespace Math

variable {V : Type*} {G : SimpleGraph V} {S S' : Finset V} {s t : ℕ} {v : V}

/-- `A` is a set of vertices, all pairs of which are adjacent (a "red" clique). -/

lemma ram_3_4_of_card_eq (hS : S.card = 9) : Ram G S 3 4 := by
  by_contra hcon
  have hdeg : ∀ v ∈ S, (redN G S v).card = 3 := by
    intro v hv
    have hcards := card_redN_add_card_blueN (G := G) hv
    have h1 : ¬ (4 ≤ (redN G S v).card) := by
      intro h4
      exact hcon (ram_succ_left hv (ram_two_left h4))
    have h2 : ¬ (6 ≤ (blueN G S v).card) := by
      intro h6
      exact hcon (ram_succ_right hv (ram_3_3 h6))
    omega
  have hsum : ∑ v ∈ S, (redN G S v).card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hS, smul_eq_mul]
  have := even_sum_card_redN G S
  rw [hsum] at this
  exact (by decide : ¬ Even 27) this

