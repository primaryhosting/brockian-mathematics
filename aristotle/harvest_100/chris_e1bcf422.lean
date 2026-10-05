import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace QC

/-- The state space of 4 qubits: the complex Hilbert space with orthonormal basis
indexed by bit strings `Fin 4 → Fin 2`. -/
abbrev Qubits4 : Type := EuclideanSpace ℂ (Fin 4 → Fin 2)

/-- The all-zeros bit string `0000`. -/
def allZeros : Fin 4 → Fin 2 := fun _ => 0

/-- The all-ones bit string `1111`. -/
def allOnes : Fin 4 → Fin 2 := fun _ => 1

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`. -/
noncomputable def ghz4 : Qubits4 :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) •
    (EuclideanSpace.single allZeros 1 + EuclideanSpace.single allOnes 1)

lemma allZeros_ne_allOnes : allZeros ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

/-- The amplitudes of the GHZ state: `1/√2` on `|0000⟩` and `|1111⟩`, zero elsewhere. -/
lemma ghz4_apply (v : Fin 4 → Fin 2) :
    ghz4.ofLp v =
      if v = allZeros then ((1 / Real.sqrt 2 : ℝ) : ℂ)
      else if v = allOnes then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0 := by
  by_cases h0 : v = allZeros
  · simp [ghz4, h0, EuclideanSpace.single_apply, allZeros_ne_allOnes]
  · by_cases h1 : v = allOnes <;>
      simp [ghz4, h0, h1, EuclideanSpace.single_apply, Ne.symm allZeros_ne_allOnes]

/-- **The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector.** -/
theorem ghz4_normalized : ‖ghz4‖ = 1 := by
  have hamp : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), div_pow, one_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hsum : ∑ v : Fin 4 → Fin 2, ‖ghz4.ofLp v‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_add_of_mem allZeros allOnes (Finset.mem_univ _) (Finset.mem_univ _)
      allZeros_ne_allOnes]
    · rw [ghz4_apply, ghz4_apply, if_pos rfl, if_neg (Ne.symm allZeros_ne_allOnes), if_pos rfl,
        hamp]
      norm_num
    · intro c _ hc
      rw [ghz4_apply, if_neg hc.1, if_neg hc.2]
      simp
  rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_one]

end QC

