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

/-
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain block comment; it is repeated verbatim below.)

import Mathlib

/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate

variable {n : ℕ}

/-- A (pure) state of an `n`-level system, given by its amplitude vector. -/
abbrev State (n : ℕ) := Fin n → ℂ

/-- The amplitude vector of the tensor product `ψ ⊗ φ` of two states. -/
def tens (ψ φ : State n) : Fin n × Fin n → ℂ := fun p => ψ p.1 * φ p.2

/-- The Hadamard gate acting on the ancilla qubit of a
`(qubit) ⊗ (n-level) ⊗ (n-level)` register. -/
noncomputable def hadAnc (s : Fin 2 × (Fin n × Fin n) → ℂ) :
    Fin 2 × (Fin n × Fin n) → ℂ :=
  fun q => (s (0, q.2) + (if q.1 = 0 then 1 else -1) * s (1, q.2)) / (Real.sqrt 2 : ℝ)

/-- The controlled-SWAP (Fredkin) gate: it swaps the two `n`-level registers exactly
when the ancilla qubit is `1`. -/
def cswap (s : Fin 2 × (Fin n × Fin n) → ℂ) : Fin 2 × (Fin n × Fin n) → ℂ :=
  fun q => if q.1 = 0 then s q else s (q.1, (q.2.2, q.2.1))

/-- The input state of the swap test: ancilla `|0⟩`, then `ψ ⊗ φ`. -/
def init (ψ φ : State n) : Fin 2 × (Fin n × Fin n) → ℂ :=
  fun q => if q.1 = 0 then tens ψ φ q.2 else 0

/-- The state at the end of the swap test circuit: Hadamard, controlled-SWAP, Hadamard. -/
noncomputable def swapTestFinal (ψ φ : State n) : Fin 2 × (Fin n × Fin n) → ℂ :=
  hadAnc (cswap (hadAnc (init ψ φ)))

/-- The probability that the swap test *accepts*, i.e. that measuring the ancilla
in the computational basis yields `0`. -/
noncomputable def acceptProb (ψ φ : State n) : ℝ :=
  ∑ p : Fin n × Fin n, ‖swapTestFinal ψ φ (0, p)‖ ^ 2

/-- The overlap `⟨ψ|φ⟩`. -/
noncomputable def overlap (ψ φ : State n) : ℂ := ∑ i, conj (ψ i) * φ i

lemma sqrt_two_sq_complex : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The accepting amplitudes of the swap test are the symmetrized amplitudes
`(ψ_i φ_j + ψ_j φ_i)/2`. -/
lemma swapTestFinal_zero (ψ φ : State n) (p : Fin n × Fin n) :
    swapTestFinal ψ φ (0, p) = (ψ p.1 * φ p.2 + ψ p.2 * φ p.1) / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  simp only [swapTestFinal, hadAnc, cswap, init, tens]
  norm_num
  field_simp
  rw [← sqrt_two_sq_complex]
  ring

/-- `‖z‖²` as a complex number is `z * conj z` (`Complex.mul_conj`). -/
lemma normSq_eq_mul_conj (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj]
  norm_cast
  exact (Complex.normSq_eq_norm_sq z).symm

/-- The symmetrized amplitudes have total weight `(1 + ⟨ψ|φ⟩ conj ⟨ψ|φ⟩)/2` when the
states are normalized: the purely algebraic core of the computation. -/
lemma sum_symmetrized (ψ φ : State n) :
    ∑ p : Fin n × Fin n, ((ψ p.1 * φ p.2 + ψ p.2 * φ p.1) / 2) *
        conj ((ψ p.1 * φ p.2 + ψ p.2 * φ p.1) / 2)
      = ((∑ i, ψ i * conj (ψ i)) * (∑ j, φ j * conj (φ j))
          + (∑ i, conj (ψ i) * φ i) * (∑ j, ψ j * conj (φ j))) / 2 := by
  set A : Fin n → Fin n → ℂ := fun i j => (ψ i * conj (ψ i)) * (φ j * conj (φ j)) with hA
  set B : Fin n → Fin n → ℂ := fun i j => (φ i * conj (ψ i)) * (ψ j * conj (φ j)) with hB
  have hcommA : ∑ i, ∑ j, A j i = ∑ i, ∑ j, A i j := Finset.sum_comm
  have hcommB : ∑ i, ∑ j, B j i = ∑ i, ∑ j, B i j := Finset.sum_comm
  have step1 : ∑ p : Fin n × Fin n, ((ψ p.1 * φ p.2 + ψ p.2 * φ p.1) / 2) *
        conj ((ψ p.1 * φ p.2 + ψ p.2 * φ p.1) / 2)
      = ∑ i, ∑ j, ((A i j + A j i + B i j + B j i) / 4) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hA, hB, map_div₀, map_add, map_mul, Complex.conj_ofNat]
    ring
  have step2 : ∑ i, ∑ j, ((A i j + A j i + B i j + B j i) / 4)
      = ((∑ i, ∑ j, A i j) + (∑ i, ∑ j, A j i) + (∑ i, ∑ j, B i j) + (∑ i, ∑ j, B j i)) / 4 := by
    simp only [← Finset.sum_div, ← Finset.sum_add_distrib]
  have hprodA : (∑ i, ψ i * conj (ψ i)) * (∑ j, φ j * conj (φ j)) = ∑ i, ∑ j, A i j := by
    rw [Finset.sum_mul_sum]
  have hprodB : (∑ i, conj (ψ i) * φ i) * (∑ j, ψ j * conj (φ j)) = ∑ i, ∑ j, B i j := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp only [hB]; ring
  rw [step1, step2, hcommA, hcommB, hprodA, hprodB]
  ring

/-- **Swap test.** For normalized states `ψ` and `φ`, the swap test (Hadamard on the
ancilla, controlled-SWAP, Hadamard, measure the ancilla) accepts, i.e. yields outcome
`0`, with probability `(1 + |⟨ψ|φ⟩|²)/2`. -/
theorem swap_test_overlap (ψ φ : State n)
    (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) (hφ : ∑ i, ‖φ i‖ ^ 2 = 1) :
    acceptProb ψ φ = (1 + ‖overlap ψ φ‖ ^ 2) / 2 := by
  have hψC : ∑ i, ψ i * conj (ψ i) = 1 := by
    have h : ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) = ∑ i, ψ i * conj (ψ i) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => normSq_eq_mul_conj (ψ i)
    rw [← h, hψ]; norm_num
  have hφC : ∑ i, φ i * conj (φ i) = 1 := by
    have h : ((∑ i, ‖φ i‖ ^ 2 : ℝ) : ℂ) = ∑ i, φ i * conj (φ i) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => normSq_eq_mul_conj (φ i)
    rw [← h, hφ]; norm_num
  have hconj : conj (overlap ψ φ) = ∑ j, ψ j * conj (φ j) := by
    simp only [overlap, map_sum, map_mul, Complex.conj_conj]
  have main : ((acceptProb ψ φ : ℝ) : ℂ) = (((1 + ‖overlap ψ φ‖ ^ 2) / 2 : ℝ) : ℂ) := by
    have hL : ((acceptProb ψ φ : ℝ) : ℂ)
        = ∑ p : Fin n × Fin n, ((ψ p.1 * φ p.2 + ψ p.2 * φ p.1) / 2) *
            conj ((ψ p.1 * φ p.2 + ψ p.2 * φ p.1) / 2) := by
      simp only [acceptProb, swapTestFinal_zero]
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun p _ => normSq_eq_mul_conj _
    have hR : (((1 + ‖overlap ψ φ‖ ^ 2) / 2 : ℝ) : ℂ)
        = (1 + overlap ψ φ * conj (overlap ψ φ)) / 2 := by
      rw [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, normSq_eq_mul_conj]
      norm_num
    rw [hL, hR, sum_symmetrized, hψC, hφC, hconj, overlap]
    ring
  exact_mod_cast main

/-- The rejecting amplitudes of the swap test are the antisymmetrized amplitudes
`(ψ_i φ_j - ψ_j φ_i)/2`. -/
lemma swapTestFinal_one (ψ φ : State n) (p : Fin n × Fin n) :
    swapTestFinal ψ φ (1, p) = (ψ p.1 * φ p.2 - ψ p.2 * φ p.1) / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  simp only [swapTestFinal, hadAnc, cswap, init, tens]
  norm_num
  field_simp
  rw [← sqrt_two_sq_complex]
  ring

/-- The probability that the swap test *rejects*, i.e. that measuring the ancilla
yields `1`. -/
noncomputable def rejectProb (ψ φ : State n) : ℝ :=
  ∑ p : Fin n × Fin n, ‖swapTestFinal ψ φ (1, p)‖ ^ 2

lemma sum_antisymmetrized (ψ φ : State n) :
    ∑ p : Fin n × Fin n, ((ψ p.1 * φ p.2 - ψ p.2 * φ p.1) / 2) *
        conj ((ψ p.1 * φ p.2 - ψ p.2 * φ p.1) / 2)
      = ((∑ i, ψ i * conj (ψ i)) * (∑ j, φ j * conj (φ j))
          - (∑ i, conj (ψ i) * φ i) * (∑ j, ψ j * conj (φ j))) / 2 := by
  set A : Fin n → Fin n → ℂ := fun i j => (ψ i * conj (ψ i)) * (φ j * conj (φ j)) with hA
  set B : Fin n → Fin n → ℂ := fun i j => (φ i * conj (ψ i)) * (ψ j * conj (φ j)) with hB
  have hcommA : ∑ i, ∑ j, A j i = ∑ i, ∑ j, A i j := Finset.sum_comm
  have hcommB : ∑ i, ∑ j, B j i = ∑ i, ∑ j, B i j := Finset.sum_comm
  have step1 : ∑ p : Fin n × Fin n, ((ψ p.1 * φ p.2 - ψ p.2 * φ p.1) / 2) *
        conj ((ψ p.1 * φ p.2 - ψ p.2 * φ p.1) / 2)
      = ∑ i, ∑ j, ((A i j + A j i - B i j - B j i) / 4) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hA, hB, map_div₀, map_sub, map_mul, Complex.conj_ofNat]
    ring
  have step2 : ∑ i, ∑ j, ((A i j + A j i - B i j - B j i) / 4)
      = ((∑ i, ∑ j, A i j) + (∑ i, ∑ j, A j i) - (∑ i, ∑ j, B i j) - (∑ i, ∑ j, B j i)) / 4 := by
    simp only [← Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  have hprodA : (∑ i, ψ i * conj (ψ i)) * (∑ j, φ j * conj (φ j)) = ∑ i, ∑ j, A i j := by
    rw [Finset.sum_mul_sum]
  have hprodB : (∑ i, conj (ψ i) * φ i) * (∑ j, ψ j * conj (φ j)) = ∑ i, ∑ j, B i j := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp only [hB]; ring
  rw [step1, step2, hcommA, hcommB, hprodA, hprodB]
  ring

/-- The swap test rejects with probability `(1 - |⟨ψ|φ⟩|²)/2`. -/
theorem swap_test_reject (ψ φ : State n)
    (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) (hφ : ∑ i, ‖φ i‖ ^ 2 = 1) :
    rejectProb ψ φ = (1 - ‖overlap ψ φ‖ ^ 2) / 2 := by
  have hψC : ∑ i, ψ i * conj (ψ i) = 1 := by
    have h : ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) = ∑ i, ψ i * conj (ψ i) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => normSq_eq_mul_conj (ψ i)
    rw [← h, hψ]; norm_num
  have hφC : ∑ i, φ i * conj (φ i) = 1 := by
    have h : ((∑ i, ‖φ i‖ ^ 2 : ℝ) : ℂ) = ∑ i, φ i * conj (φ i) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => normSq_eq_mul_conj (φ i)
    rw [← h, hφ]; norm_num
  have hconj : conj (overlap ψ φ) = ∑ j, ψ j * conj (φ j) := by
    simp only [overlap, map_sum, map_mul, Complex.conj_conj]
  have main : ((rejectProb ψ φ : ℝ) : ℂ) = (((1 - ‖overlap ψ φ‖ ^ 2) / 2 : ℝ) : ℂ) := by
    have hL : ((rejectProb ψ φ : ℝ) : ℂ)
        = ∑ p : Fin n × Fin n, ((ψ p.1 * φ p.2 - ψ p.2 * φ p.1) / 2) *
            conj ((ψ p.1 * φ p.2 - ψ p.2 * φ p.1) / 2) := by
      simp only [rejectProb, swapTestFinal_one]
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun p _ => normSq_eq_mul_conj _
    have hR : (((1 - ‖overlap ψ φ‖ ^ 2) / 2 : ℝ) : ℂ)
        = (1 - overlap ψ φ * conj (overlap ψ φ)) / 2 := by
      rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, normSq_eq_mul_conj]
      norm_num
    rw [hL, hR, sum_antisymmetrized, hψC, hφC, hconj, overlap]
    ring
  exact_mod_cast main

/-- Sanity check (unitarity): the two outcome probabilities sum to `1`. -/
theorem swap_test_total (ψ φ : State n)
    (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) (hφ : ∑ i, ‖φ i‖ ^ 2 = 1) :
    acceptProb ψ φ + rejectProb ψ φ = 1 := by
  rw [swap_test_overlap ψ φ hψ hφ, swap_test_reject ψ φ hψ hφ]
  ring

/-- Sanity check: the swap test always accepts two copies of the same normalized state. -/
theorem swap_test_self (ψ : State n) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    acceptProb ψ ψ = 1 := by
  have hov : overlap ψ ψ = 1 := by
    have : overlap ψ ψ = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine (Finset.sum_congr rfl fun i _ => ?_).symm
      rw [normSq_eq_mul_conj]
      ring
    rw [this, hψ]; norm_num
  rw [swap_test_overlap ψ ψ hψ hψ, hov]
  norm_num

end QC

#print axioms QC.swap_test_overlap
#print axioms QC.swap_test_total

