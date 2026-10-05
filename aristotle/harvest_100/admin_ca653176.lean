import Mathlib

/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- Index type for the computational basis of 6 qubits: bitstrings of length 6. -/
abbrev Q6 := Fin 6 → Bool

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, as a vector in the
`64`-dimensional complex Hilbert space `EuclideanSpace ℂ (Fin 6 → Bool)`. -/
noncomputable def ghz6 : EuclideanSpace ℂ Q6 :=
  WithLp.toLp 2 fun b : Q6 =>
    if b = (fun _ => false) ∨ b = (fun _ => true) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The 6-qubit GHZ state is a unit vector. -/
theorem ghz6_normalized : ‖ghz6‖ = 1 := by
  have hne : (fun _ => false : Q6) ≠ (fun _ => true) := by
    intro h
    have := congrFun h 0
    simp at this
  have key : ∀ b : Q6, ‖ghz6.ofLp b‖ ^ 2
      = if b ∈ ({(fun _ => false), (fun _ => true)} : Finset Q6) then (1 / 2 : ℝ) else 0 := by
    intro b
    simp only [ghz6, WithLp.ofLp_toLp, Finset.mem_insert, Finset.mem_singleton]
    by_cases h : b = (fun _ => false) ∨ b = (fun _ => true)
    · rw [if_pos h, if_pos h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_pow, one_pow, Real.sq_sqrt (by norm_num)]
    · rw [if_neg h, if_neg h]
      simp
  rw [EuclideanSpace.norm_eq, Finset.sum_congr rfl fun b _ => key b,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  norm_num

end QC

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

