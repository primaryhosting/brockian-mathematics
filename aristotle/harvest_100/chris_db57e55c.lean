/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Language Computability

/-- `pump y i` is the concatenation of `i` copies of the word `y`. -/
def pump {α : Type*} (y : List α) (i : ℕ) : List α :=
  (List.replicate i y).flatten

lemma pump_mem_kstar {α : Type*} (y : List α) (i : ℕ) : pump y i ∈ ({y} : Language α)∗ := by
  rw [Language.mem_kstar]
  refine ⟨List.replicate i y, rfl, ?_⟩
  intro z hz
  simpa using List.eq_of_mem_replicate hz

/--
**Pumping lemma for regular languages.**

Every regular language `L` admits a pumping length `p > 0`: every word `w ∈ L` of length at
least `p` can be split as `w = x ++ y ++ z` with `|x ++ y| ≤ p` and `y ≠ []`, in such a way
that `x ++ yⁱ ++ z ∈ L` for every `i : ℕ`.

The core combinatorial content is Mathlib's `DFA.pumping_lemma`.
-/
theorem pumping_regular {α : Type*} {L : Language α} (hL : L.IsRegular) :
    ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length →
      ∃ x y z : List α, w = x ++ y ++ z ∧ x.length + y.length ≤ p ∧ y ≠ [] ∧
        ∀ i : ℕ, x ++ pump y i ++ z ∈ L := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  refine ⟨Fintype.card σ, ?_, ?_⟩
  · exact Fintype.card_pos_iff.mpr ⟨M.start⟩
  · intro w hw hlen
    obtain ⟨x, y, z, hsplit, hxy, hy, hsub⟩ := M.pumping_lemma hw hlen
    refine ⟨x, y, z, hsplit, hxy, hy, fun i => ?_⟩
    refine hsub ?_
    rw [Language.mem_mul]
    refine ⟨x ++ pump y i, ?_, z, rfl, rfl⟩
    rw [Language.mem_mul]
    exact ⟨x, rfl, pump y i, pump_mem_kstar y i, rfl⟩

end CS

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

