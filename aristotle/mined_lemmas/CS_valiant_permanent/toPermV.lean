import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

def toPermV : Equiv.Perm (Vert A) where
  toFun := fun v => match v with
    | Sum.inl i => Sum.inr (cellOf A π k i)
    | Sum.inr c => if c = cellOf A π k c.1.1 then Sum.inl c.1.2 else Sum.inr c
  invFun := fun v => match v with
    | Sum.inl j => Sum.inr (cellOf A π k (π.symm j))
    | Sum.inr c => if c = cellOf A π k c.1.1 then Sum.inl c.1.1 else Sum.inr c
  left_inv := by
    rintro (i | c)
    · show (if cellOf A π k i = cellOf A π k (cellOf A π k i).1.1 then
          (Sum.inl (cellOf A π k i).1.1 : Vert A) else Sum.inr (cellOf A π k i)) = Sum.inl i
      rw [show (cellOf A π k i).1.1 = i from rfl, if_pos rfl]
    · by_cases h : c = cellOf A π k c.1.1
      · have h2 : c.1.2 = π c.1.1 := snd_of_used A π k h
        show (match (if c = cellOf A π k c.1.1 then (Sum.inl c.1.2 : Vert A) else Sum.inr c) with
          | Sum.inl j => (Sum.inr (cellOf A π k (π.symm j)) : Vert A)
          | Sum.inr d => if d = cellOf A π k d.1.1 then Sum.inl d.1.1 else Sum.inr d) = Sum.inr c
        rw [if_pos h]
        simp only [h2, Equiv.symm_apply_apply]
        exact congrArg Sum.inr h.symm
      · show (match (if c = cellOf A π k c.1.1 then (Sum.inl c.1.2 : Vert A) else Sum.inr c) with
          | Sum.inl j => (Sum.inr (cellOf A π k (π.symm j)) : Vert A)
          | Sum.inr d => if d = cellOf A π k d.1.1 then Sum.inl d.1.1 else Sum.inr d) = Sum.inr c
        rw [if_neg h]
        show (if c = cellOf A π k c.1.1 then (Sum.inl c.1.1 : Vert A) else Sum.inr c) = Sum.inr c
        rw [if_neg h]
  right_inv := by
    rintro (j | c)
    · show (if cellOf A π k (π.symm j) = cellOf A π k (cellOf A π k (π.symm j)).1.1 then
          (Sum.inl (cellOf A π k (π.symm j)).1.2 : Vert A)
          else Sum.inr (cellOf A π k (π.symm j))) = Sum.inl j
      rw [show (cellOf A π k (π.symm j)).1.1 = π.symm j from rfl, if_pos rfl,
        show (cellOf A π k (π.symm j)).1.2 = π (π.symm j) from rfl]
      simp
    · by_cases h : c = cellOf A π k c.1.1
      · show (match (if c = cellOf A π k c.1.1 then (Sum.inl c.1.1 : Vert A) else Sum.inr c) with
          | Sum.inl i => (Sum.inr (cellOf A π k i) : Vert A)
          | Sum.inr d => if d = cellOf A π k d.1.1 then Sum.inl d.1.2 else Sum.inr d) = Sum.inr c
        rw [if_pos h]
        exact congrArg Sum.inr h.symm
      · show (match (if c = cellOf A π k c.1.1 then (Sum.inl c.1.1 : Vert A) else Sum.inr c) with
          | Sum.inl i => (Sum.inr (cellOf A π k i) : Vert A)
          | Sum.inr d => if d = cellOf A π k d.1.1 then Sum.inl d.1.2 else Sum.inr d) = Sum.inr c
        rw [if_neg h]
        show (if c = cellOf A π k c.1.1 then (Sum.inl c.1.2 : Vert A) else Sum.inr c) = Sum.inr c
        rw [if_neg h]

