/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma powerset_filter_eq_D {N n : ℕ} (hN : n ≤ N) :
    (Finset.Icc 1 N).powerset.filter (fun S => ∑ i ∈ S, i = n) = D n := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, mem_D_iff]
  constructor
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum⟩
    have := hsub h0
    simp only [Finset.mem_Icc] at this
    omega
  · rintro ⟨h0, hsum⟩
    refine ⟨fun x hx => ?_, hsum⟩
    have hx1 : 1 ≤ x := by
      rcases Nat.eq_zero_or_pos x with h | h
      · exact absurd (h ▸ hx) h0
      · exact h
    have hxn : x ≤ n := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    simp only [Finset.mem_Icc]
    omega

/-- Splitting a sum over `[-n, n] ⊆ ℤ` into the term at `0` and the positive and negative parts. -/
