import Mathlib
/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to come before any command, including module
-- doc comments (`/-! ... -/`), so the requested header appears immediately after the
-- single `import Mathlib` line.

namespace QC

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, viewed as a vector in the
Hilbert space `EuclideanSpace ℂ (Fin 6 → Bool)` whose coordinates are indexed by
the computational basis states `Fin 6 → Bool`. -/
noncomputable def ghz6 : EuclideanSpace ℂ (Fin 6 → Bool) :=
  WithLp.toLp 2 fun b =>
    if b = (fun _ => false) ∨ b = (fun _ => true) then ((Real.sqrt 2)⁻¹ : ℝ) else 0

/-- `ghz6` really is the superposition `(|000000⟩ + |111111⟩)/√2`: it equals `(√2)⁻¹`
times the sum of the two computational basis vectors `|000000⟩` and `|111111⟩`. -/
theorem ghz6_eq_superposition :
    ghz6 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (EuclideanSpace.single (fun _ => false) (1 : ℂ)
        + EuclideanSpace.single (fun _ => true) (1 : ℂ)) := by
  have hne : ((fun _ => true : Fin 6 → Bool)) ≠ (fun _ => false) := by
    intro hcon
    have := congrFun hcon 0
    simp at this
  ext b
  simp only [ghz6, WithLp.ofLp_toLp, PiLp.smul_apply, PiLp.add_apply,
    EuclideanSpace.single_apply, smul_eq_mul]
  by_cases h0 : b = (fun _ => false)
  · subst h0; simp [hne.symm]
  · by_cases h1 : b = (fun _ => true) <;> simp [h0, h1, hne]

/-- The 6-qubit GHZ state is a unit vector. -/
theorem ghz6_normalized : ‖ghz6‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ b : Fin 6 → Bool, ‖ghz6.ofLp b‖ ^ 2 =
      if b ∈ ({(fun _ => false), (fun _ => true)} : Finset (Fin 6 → Bool)) then (2 : ℝ)⁻¹
      else 0 := by
    intro b
    simp only [ghz6, WithLp.ofLp_toLp, Finset.mem_insert, Finset.mem_singleton]
    split
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        ← Real.sqrt_inv, Real.sq_sqrt (by norm_num)]
    · simp
  have hcard : ({(fun _ => false), (fun _ => true)} : Finset (Fin 6 → Bool)).card = 2 := by
    rw [Finset.card_pair]
    intro hcon
    have := congrFun hcon 0
    simp at this
  simp only [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hcard]
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

