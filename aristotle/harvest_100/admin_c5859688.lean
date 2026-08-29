/-
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector in the complex
Hilbert space whose orthonormal basis is the computational basis `Fin 5 → Bool`. -/
noncomputable def ghz5 : EuclideanSpace ℂ (Fin 5 → Bool) :=
  WithLp.toLp 2 fun x =>
    if x = (fun _ => false) ∨ x = (fun _ => true) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The 5-qubit GHZ state is a unit vector. -/
theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  have h2 : ((1 : ℝ) / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hs : ∀ x : Fin 5 → Bool,
      ‖ghz5.ofLp x‖ ^ 2 =
        if x ∈ ({(fun _ => false), (fun _ => true)} : Finset (Fin 5 → Bool)) then
          (1 / 2 : ℝ) else 0 := by
    intro x
    by_cases h : x = (fun _ => false) ∨ x = (fun _ => true)
    · have hmem : x ∈ ({(fun _ => false), (fun _ => true)} : Finset (Fin 5 → Bool)) := by
        simp [Finset.mem_insert, Finset.mem_singleton, h]
      simp only [ghz5, WithLp.ofLp_toLp, if_pos h, if_pos hmem, Complex.norm_real,
        Real.norm_eq_abs, ← abs_pow, h2]
      norm_num
    · simp [ghz5, if_neg h]
  have hne : (fun _ => false) ∉ ({(fun _ => true)} : Finset (Fin 5 → Bool)) := by
    simp only [Finset.mem_singleton]
    intro hc
    have := congrFun hc 0
    simp at this
  have hcard : ({(fun _ => false), (fun _ => true)} : Finset (Fin 5 → Bool)).card = 2 := by
    rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]
  have hsum : ∑ x : Fin 5 → Bool, ‖ghz5.ofLp x‖ ^ 2 = 1 := by
    rw [Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, hcard]
    norm_num
  rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_one]

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

