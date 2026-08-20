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

lemma card_nbr_add_card_nbr_compl {v : V} {W : Finset V} (hv : v ∈ W) :
    (nbr G v W).card + (nbr Gᶜ v W).card = W.card - 1 := by
  have h1 : nbr G v W = (W.erase v).filter (fun w => G.Adj v w) := by
    ext w
    simp only [mem_nbr, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hw, hadj⟩; exact ⟨⟨(G.ne_of_adj hadj).symm, hw⟩, hadj⟩
    · rintro ⟨⟨_, hw⟩, hadj⟩; exact ⟨hw, hadj⟩
  have h2 : nbr Gᶜ v W = (W.erase v).filter (fun w => ¬ G.Adj v w) := by
    ext w
    simp only [mem_nbr, Finset.mem_filter, Finset.mem_erase, SimpleGraph.compl_adj]
    constructor
    · rintro ⟨hw, hne, hadj⟩; exact ⟨⟨fun h => hne h.symm, hw⟩, hadj⟩
    · rintro ⟨⟨hne, hw⟩, hadj⟩; exact ⟨hw, fun h => hne h.symm, hadj⟩
  rw [h1, h2, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]

/-- `Mono G r s W` : the subset `W` contains an `r`-clique of `G` or an `s`-clique of `Gᶜ`. -/
