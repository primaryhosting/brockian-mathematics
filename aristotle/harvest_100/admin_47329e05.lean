/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Computability

universe u

namespace CS

/-- Auxiliary: the concatenation of `n` copies of `y` lies in the Kleene star of `{y}`. -/
theorem flatten_replicate_mem_kstar {α : Type u} (y : List α) (n : ℕ) :
    (List.replicate n y).flatten ∈ ({y} : Language α)∗ := by
  rw [Language.mem_kstar]
  refine ⟨List.replicate n y, rfl, ?_⟩
  intro z hz
  rw [List.eq_of_mem_replicate hz]
  exact Set.mem_singleton _

/-- **Pumping lemma for regular languages.**

Every regular language `L` admits a pumping length `p > 0` such that every word `w ∈ L` of
length at least `p` can be split as `w = x ++ y ++ z` with `y` nonempty and `(x ++ y).length ≤ p`,
in such a way that `x ++ yⁿ ++ z ∈ L` for every `n : ℕ`. -/
theorem pumping_regular {α : Type u} (L : Language α) (hL : L.IsRegular) :
    ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length →
      ∃ x y z : List α, w = x ++ y ++ z ∧ y ≠ [] ∧ (x ++ y).length ≤ p ∧
        ∀ n : ℕ, x ++ (List.replicate n y).flatten ++ z ∈ L := by
  obtain ⟨σ, hfin, M, rfl⟩ := hL
  have hne : Nonempty σ := ⟨M.start⟩
  refine ⟨Fintype.card σ, Fintype.card_pos, ?_⟩
  intro w hw hlen
  obtain ⟨x, y, z, hsplit, hxy, hy, hsub⟩ := M.pumping_lemma hw hlen
  refine ⟨x, y, z, hsplit, hy, by simpa using hxy, ?_⟩
  intro n
  refine hsub ?_
  rw [Language.mem_mul]
  refine ⟨x ++ (List.replicate n y).flatten, ?_, z, Set.mem_singleton _, by simp⟩
  rw [Language.mem_mul]
  exact ⟨x, Set.mem_singleton _, _, flatten_replicate_mem_kstar y n, rfl⟩

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

