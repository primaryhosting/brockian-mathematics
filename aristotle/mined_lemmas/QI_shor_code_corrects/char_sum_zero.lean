/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command, so the header above is written as a
-- plain block comment rather than a `/-!` module docstring.)

import Mathlib

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## The 9-qubit register

We label the nine qubits by `Site = Fin 3 × Fin 3`: the first coordinate is the *block*
(one of three three-qubit repetition blocks) and the second the position inside the block.
A computational basis state is a bit string `Bits = Site → ZMod 2`, and a state vector is
its amplitude function `Amp = Bits → ℂ`.
-/

abbrev Site : Type := Fin 3 × Fin 3

abbrev Bits : Type := Site → ZMod 2

abbrev Amp : Type := Bits → ℂ

/-- The Hermitian inner product `⟪u, v⟫ = ∑_b conj (u b) * v b`. -/

lemma char_sum_zero (w : Fin 3 → ZMod 2) (r0 : Fin 3) (hw : w r0 = 1) :
    ∑ c : Fin 3 → ZMod 2, sgn (∑ r : Fin 3, w r * c r) = 0 := by
  set d : Fin 3 → ZMod 2 := fun r => if r = r0 then 1 else 0 with hd
  set S : ℂ := ∑ c : Fin 3 → ZMod 2, sgn (∑ r : Fin 3, w r * c r) with hS
  have key : S = -S := by
    calc S = ∑ c : Fin 3 → ZMod 2, sgn (∑ r : Fin 3, w r * ((Equiv.addRight d) c) r) := by
            rw [hS, Equiv.sum_comp (Equiv.addRight d)
              (fun c => sgn (∑ r : Fin 3, w r * c r))]
      _ = -S := by
            rw [hS, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun c _ => ?_
            have hsum : ∑ r : Fin 3, w r * ((Equiv.addRight d) c) r
                = (∑ r : Fin 3, w r * c r) + 1 := by
              simp only [Equiv.coe_addRight, Pi.add_apply, mul_add]
              rw [Finset.sum_add_distrib]
              congr 1
              rw [hd]
              simp [Finset.sum_ite_eq' Finset.univ r0, hw]
            rw [hsum, sgn_add, sgn_one]
            ring
  have : (2 : ℂ) * S = 0 := by rw [two_mul]; nth_rewrite 2 [key]; ring
  simpa using this

