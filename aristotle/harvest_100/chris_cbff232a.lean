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

namespace QC

/-- The all-zeros bitstring on 8 qubits, i.e. the index of `|0…0⟩`. -/
def allZeros : Fin 8 → Fin 2 := fun _ => 0

/-- The all-ones bitstring on 8 qubits, i.e. the index of `|1…1⟩`. -/
def allOnes : Fin 8 → Fin 2 := fun _ => 1

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector in the
`2^8`-dimensional complex Hilbert space with orthonormal basis indexed by
bitstrings `Fin 8 → Fin 2`. -/
noncomputable def ghz8 : EuclideanSpace ℂ (Fin 8 → Fin 2) :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
    (EuclideanSpace.single allZeros 1 + EuclideanSpace.single allOnes 1)

lemma allZeros_ne_allOnes : allZeros ≠ allOnes := by
  intro h
  have := congrFun h ⟨0, by norm_num⟩
  simp [allZeros, allOnes] at this

/-- The coordinates of the GHZ state: `1/√2` on `|0…0⟩` and `|1…1⟩`, zero elsewhere. -/
lemma ghz8_apply (b : Fin 8 → Fin 2) :
    ghz8 b = if b = allZeros ∨ b = allOnes then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0 := by
  have hne : allZeros ≠ allOnes := allZeros_ne_allOnes
  by_cases h0 : b = allZeros
  · subst h0; simp [ghz8, EuclideanSpace.single_apply, hne]
  · by_cases h1 : b = allOnes
    · subst h1; simp [ghz8, EuclideanSpace.single_apply, Ne.symm hne]
    · simp [ghz8, EuclideanSpace.single_apply, h0, h1]

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
theorem ghz8_normalized : ‖ghz8‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsq : ∀ b : Fin 8 → Fin 2,
      ‖ghz8 b‖ ^ 2 = if b = allZeros ∨ b = allOnes then (2 : ℝ)⁻¹ else 0 := by
    intro b
    rw [ghz8_apply b]
    by_cases hb : b = allZeros ∨ b = allOnes <;>
      simp [hb, Complex.norm_real, abs_of_nonneg, Real.sq_sqrt]
  have hmem : ∀ b : Fin 8 → Fin 2,
      (b = allZeros ∨ b = allOnes) ↔ b ∈ ({allZeros, allOnes} : Finset (Fin 8 → Fin 2)) := by
    intro b; simp
  have hsum : ∑ b : Fin 8 → Fin 2, ‖ghz8 b‖ ^ 2 = 1 := by
    simp only [hsq, hmem]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.card_insert_of_notMem (by
        simpa [Finset.mem_singleton] using allZeros_ne_allOnes)]
    norm_num
  rw [hsum, Real.sqrt_one]

end QC

