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

namespace Chem

open Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₄`, viewed with vertex set `ZMod 14`
(which is definitionally `Fin 14`). -/

lemma sum_ch (c : ZMod 14) : (∑ j : ZMod 14, ch (j * c)) = if c = 0 then 14 else 0 := by
  by_cases hc : c = 0
  · subst hc; simp [ch_zero]
  · simp only [hc, if_false]
    set S : ℂ := ∑ j : ZMod 14, ch (j * c) with hS
    have hshift : ch c * S = S := by
      rw [hS, Finset.mul_sum]
      have : ∀ j : ZMod 14, ch c * ch (j * c) = ch ((j + 1) * c) := by
        intro j
        rw [← ch_add]
        ring_nf
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod 14)) _ _ (fun j => rfl)
    have hne : ch c ≠ 1 := fun h => hc ((ch_eq_one_iff c).1 h)
    have : (ch c - 1) * S = 0 := by linear_combination hshift
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h

/-- The (unnormalised) discrete Fourier matrix. -/
