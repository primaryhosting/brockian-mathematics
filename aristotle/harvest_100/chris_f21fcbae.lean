/-
# Ghz 3 Normalized
Category: Quantum Computing
Target: QC.ghz3_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 3 Normalized
Category: Quantum Computing
Target: QC.ghz3_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

/-- The state space of three qubits: the (complex) Euclidean space indexed by the
computational basis states, i.e. by bitstrings `Fin 3 → Fin 2`. -/
abbrev Qubits3 : Type := EuclideanSpace ℂ (Fin 3 → Fin 2)

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2`: its amplitude is `1/√2` on the two
basis states `|000⟩` and `|111⟩`, and `0` on every other computational basis state. -/
noncomputable def ghz3 : Qubits3 :=
  WithLp.toLp 2 (fun b : Fin 3 → Fin 2 =>
    if (∀ i, b i = 0) ∨ (∀ i, b i = 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- The GHZ state is indeed the normalized superposition `(|000⟩ + |111⟩)/√2` of the
two computational basis vectors `|000⟩` and `|111⟩`. -/
theorem ghz3_eq_superposition :
    ghz3 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single (fun _ : Fin 3 => (0 : Fin 2)) (1 : ℂ)
        + EuclideanSpace.single (fun _ : Fin 3 => (1 : Fin 2)) (1 : ℂ)) := by
  ext b
  by_cases h0 : ∀ i, b i = 0
  · have hb : b = fun _ : Fin 3 => (0 : Fin 2) := funext h0
    subst hb
    simp [ghz3, EuclideanSpace.single_apply, funext_iff]
  · by_cases h1 : ∀ i, b i = 1
    · have hb : b = fun _ : Fin 3 => (1 : Fin 2) := funext h1
      subst hb
      simp [ghz3, EuclideanSpace.single_apply, funext_iff]
    · have hn0 : b ≠ fun _ : Fin 3 => (0 : Fin 2) := fun h => h0 (fun i => by rw [h])
      have hn1 : b ≠ fun _ : Fin 3 => (1 : Fin 2) := fun h => h1 (fun i => by rw [h])
      simp [ghz3, EuclideanSpace.single_apply, h0, h1, hn0, hn1]

/-- **The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2` is a unit vector.** -/
theorem ghz3_normalized : ‖ghz3‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ b : Fin 3 → Fin 2,
      ‖ghz3.ofLp b‖ ^ 2 = if (∀ i, b i = 0) ∨ (∀ i, b i = 1) then (1 / 2 : ℝ) else 0 := by
    intro b
    by_cases hb : (∀ i, b i = 0) ∨ (∀ i, b i = 1)
    · simp only [ghz3, WithLp.ofLp_toLp, if_pos hb, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / Real.sqrt 2), div_pow, one_pow,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    · simp [ghz3, if_neg hb]
  simp only [h]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]
  have hc :
      (Finset.univ.filter (fun b : Fin 3 → Fin 2 => (∀ i, b i = 0) ∨ (∀ i, b i = 1))).card = 2 := by
    decide
  rw [hc]
  norm_num

end QC

