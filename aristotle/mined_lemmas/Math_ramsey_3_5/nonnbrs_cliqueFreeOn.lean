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

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Math

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s`, or an independent set of size `t` (a clique of size `t` in the complement).
Equivalently, every 2-colouring of the edges of `K n` has a red `K s` or a blue `K t`. -/

lemma nonnbrs_cliqueFreeOn {A : Finset V} {v : V} {t : ℕ} (hv : v ∈ A)
    (ht : Gᶜ.CliqueFreeOn (↑A) (t + 1)) : Gᶜ.CliqueFreeOn (↑(nonnbrs G A v)) t := by
  intro S hS hSclique
  have hvS : v ∉ S := by
    intro hv'
    have := hS hv'
    simp only [mem_coe, nonnbrs, mem_filter, mem_erase] at this
    exact this.1.1 rfl
  have hadj : ∀ b ∈ S, Gᶜ.Adj v b := by
    intro b hb
    have := hS hb
    simp only [mem_coe, nonnbrs, mem_filter, mem_erase] at this
    exact ⟨fun h => this.1.1 h.symm, this.2⟩
  refine ht (t := insert v S) ?_ (hSclique.insert hadj)
  intro z hz
  simp only [coe_insert, Set.mem_insert_iff] at hz
  rcases hz with rfl | hz
  · exact hv
  · exact nonnbrs_subset (hS hz)

end Tools

/-! ## A parity lemma -/

section Parity

variable {V : Type*} [DecidableEq V]

