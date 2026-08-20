/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to be the first command; the header above is repeated below
-- as a module docstring.)

import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

open Finset

/-! ## Generalities on monochromatic cliques -/

section General

variable {V : Type*} [LinearOrder V] {G : SimpleGraph V}

/-- The set of vertices of `W` adjacent to `v` in `G`. -/

theorem cliqueFree_four_of {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (h : ∀ a b c d : V, G.Adj a b → G.Adj a c → G.Adj a d → G.Adj b c → G.Adj b d → G.Adj c d →
      False) : G.CliqueFree 4 := by
  intro t ht
  obtain ⟨hclique, hcard⟩ := ht
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < t.card by omega)
  have h3 : (t.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha, hcard]
  obtain ⟨b, c, d, hbc, hbd, hcd, he⟩ := Finset.card_eq_three.mp h3
  have hb : b ∈ t.erase a := by rw [he]; simp
  have hc : c ∈ t.erase a := by rw [he]; simp
  have hd : d ∈ t.erase a := by rw [he]; simp
  exact h a b c d (hclique ha (Finset.mem_of_mem_erase hb)
      (fun h => (Finset.ne_of_mem_erase hb) h.symm))
    (hclique ha (Finset.mem_of_mem_erase hc) (fun h => (Finset.ne_of_mem_erase hc) h.symm))
    (hclique ha (Finset.mem_of_mem_erase hd) (fun h => (Finset.ne_of_mem_erase hd) h.symm))
    (hclique (Finset.mem_of_mem_erase hb) (Finset.mem_of_mem_erase hc) hbc)
    (hclique (Finset.mem_of_mem_erase hb) (Finset.mem_of_mem_erase hd) hbd)
    (hclique (Finset.mem_of_mem_erase hc) (Finset.mem_of_mem_erase hd) hcd)

