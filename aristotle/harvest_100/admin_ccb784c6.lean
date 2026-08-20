/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is kept as a plain block comment because Lean 4 does not
-- allow a module docstring `/-! ... -/` to precede the `import` command.)

import Mathlib

namespace QC

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, described as a vector in the
Hilbert space `ℂ^(Fin 8 → Bool)` of 8 qubits: its amplitude is `1/√2` on the two
computational basis states `|00000000⟩` and `|11111111⟩`, and `0` elsewhere. -/
noncomputable def ghz8 : EuclideanSpace ℂ (Fin 8 → Bool) :=
  WithLp.toLp 2
    (fun v => if (∀ i, v i = false) ∨ (∀ i, v i = true) then ((Real.sqrt 2)⁻¹ : ℝ) else 0)

/-- The 8-qubit GHZ state is a unit vector. -/
theorem ghz8_normalized : ‖ghz8‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hterm : ∀ v : Fin 8 → Bool, ‖ghz8.ofLp v‖ ^ 2 =
      if (∀ i, v i = false) ∨ (∀ i, v i = true) then (1/2 : ℝ) else 0 := by
    intro v
    by_cases h : (∀ i, v i = false) ∨ (∀ i, v i = true) <;>
      simp [ghz8, h, Complex.norm_real]
  have hsum : ∑ v : Fin 8 → Bool, ‖ghz8.ofLp v‖ ^ 2 = 1 := by
    rw [Finset.sum_congr rfl (fun v _ => hterm v), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter
        (fun v : Fin 8 → Bool => (∀ i, v i = false) ∨ (∀ i, v i = true))).card = 2 := by
      decide
    rw [hcard]
    norm_num
  rw [hsum, Real.sqrt_one]

/-- Faithfulness check: `ghz8` really is `(|0…0⟩ + |1…1⟩)/√2`, i.e. the scalar
`1/√2` times the sum of the two computational basis vectors `|00000000⟩` and
`|11111111⟩`. -/
theorem ghz8_eq : ghz8 = ((Real.sqrt 2)⁻¹ : ℝ) •
    (EuclideanSpace.single (fun _ => false) (1 : ℂ)
      + EuclideanSpace.single (fun _ => true) (1 : ℂ)) := by
  have hft : ¬ ((fun _ => false : Fin 8 → Bool) = fun _ => true) := by
    intro hcon; simpa using congrFun hcon 0
  ext v
  by_cases h0 : ∀ i, v i = false
  · have hv : v = fun _ => false := funext h0
    subst hv
    simp [ghz8, EuclideanSpace.single_apply, hft]
  · by_cases h1 : ∀ i, v i = true
    · have hv : v = fun _ => true := funext h1
      subst hv
      simp [ghz8, EuclideanSpace.single_apply, Ne.symm hft]
    · have hne0 : v ≠ fun _ => false := fun hc => h0 (fun i => by rw [hc])
      have hne1 : v ≠ fun _ => true := fun hc => h1 (fun i => by rw [hc])
      simp [ghz8, EuclideanSpace.single_apply, h0, h1, hne0, hne1]

/-- Equivalent inner-product form of normalization: `⟪ghz8, ghz8⟫ = 1`. -/
theorem ghz8_inner_self : inner ℂ ghz8 ghz8 = (1 : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K, ghz8_normalized]
  norm_num

end QC

#print axioms QC.ghz8_normalized
#print axioms QC.ghz8_eq
#print axioms QC.ghz8_inner_self

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

