import Mathlib

/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace QC

/-!
## Model

We model the SWAP test on two `n`-level registers together with one ancilla qubit.
A pure state of the whole system is a function

  `Bool × Fin n × Fin n → ℂ`,

the first component indexing the ancilla qubit.

The circuit is: prepare `|0⟩ ⊗ ψ ⊗ φ`, apply a Hadamard gate on the ancilla,
apply a controlled SWAP of the two registers (controlled on the ancilla),
apply a Hadamard gate on the ancilla again, and finally measure the ancilla.
The test *accepts* when the ancilla is measured in the state `|0⟩`.
-/

variable {n : ℕ}

/-- The Hadamard gate acting on the ancilla qubit. -/
noncomputable def hadamardAncilla (f : Bool × Fin n × Fin n → ℂ) :
    Bool × Fin n × Fin n → ℂ :=
  fun p =>
    if p.1 then (f (false, p.2) - f (true, p.2)) / (Real.sqrt 2 : ℂ)
    else (f (false, p.2) + f (true, p.2)) / (Real.sqrt 2 : ℂ)

/-- The SWAP of the two registers, controlled on the ancilla qubit. -/
def controlledSwap (f : Bool × Fin n × Fin n → ℂ) : Bool × Fin n × Fin n → ℂ :=
  fun p => if p.1 then f (true, p.2.2, p.2.1) else f (false, p.2)

/-- The initial state `|0⟩ ⊗ ψ ⊗ φ`. -/
def initialState (psi phi : Fin n → ℂ) : Bool × Fin n × Fin n → ℂ :=
  fun p => if p.1 then 0 else psi p.2.1 * phi p.2.2

/-- The state of the system just before the measurement of the ancilla. -/
noncomputable def swapTestState (psi phi : Fin n → ℂ) : Bool × Fin n × Fin n → ℂ :=
  hadamardAncilla (controlledSwap (hadamardAncilla (initialState psi phi)))

/-- The probability that the SWAP test accepts, i.e. that the ancilla is
measured in the state `|0⟩`. -/
noncomputable def acceptProb (psi phi : Fin n → ℂ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ‖swapTestState psi phi (false, i, j)‖ ^ 2

/-- The inner product `⟨ψ|φ⟩`. -/
noncomputable def overlap (psi phi : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, (starRingEnd ℂ) (psi i) * phi i

/-- The amplitude of the accepting branch of the SWAP test. -/
theorem swapTestState_false (psi phi : Fin n → ℂ) (i j : Fin n) :
    swapTestState psi phi (false, i, j) = (psi i * phi j + psi j * phi i) / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  simp only [swapTestState, hadamardAncilla, controlledSwap, initialState,
    if_true, if_false, Bool.false_eq_true]
  field_simp
  simp only [hsq]
  ring

/-- Squared-norm expansion of the accepting amplitude, summed over the registers. -/
theorem acceptProb_eq_sum (psi phi : Fin n → ℂ) :
    acceptProb psi phi
      = (1 / 4) * ∑ i : Fin n, ∑ j : Fin n,
          Complex.normSq (psi i * phi j + psi j * phi i) := by
  simp only [acceptProb, swapTestState_false, Complex.sq_norm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.normSq_div]
  simp [Complex.normSq_apply]
  ring

/-- **The SWAP test accepts with probability `(1 + |⟨ψ|φ⟩|²)/2`.** -/
theorem swap_test_overlap (psi phi : Fin n → ℂ)
    (hpsi : ∑ i : Fin n, ‖psi i‖ ^ 2 = 1) (hphi : ∑ i : Fin n, ‖phi i‖ ^ 2 = 1) :
    acceptProb psi phi = (1 + ‖overlap psi phi‖ ^ 2) / 2 := by
  have hpsi' : ∑ i : Fin n, Complex.normSq (psi i) = 1 := by
    simpa [Complex.sq_norm] using hpsi
  have hphi' : ∑ i : Fin n, Complex.normSq (phi i) = 1 := by
    simpa [Complex.sq_norm] using hphi
  -- expand each squared norm
  have hexp : ∀ i j : Fin n,
      Complex.normSq (psi i * phi j + psi j * phi i)
        = Complex.normSq (psi i) * Complex.normSq (phi j)
          + Complex.normSq (psi j) * Complex.normSq (phi i)
          + 2 * ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re := by
    intro i j
    rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul]
  -- the three pieces
  have h1 : ∑ i : Fin n, ∑ j : Fin n,
      Complex.normSq (psi i) * Complex.normSq (phi j) = 1 := by
    rw [← Finset.sum_mul_sum]
    rw [hpsi', hphi']; ring
  have h2 : ∑ i : Fin n, ∑ j : Fin n,
      Complex.normSq (psi j) * Complex.normSq (phi i) = 1 := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_mul_sum]
    rw [hpsi', hphi']; ring
  have hcross : ∑ i : Fin n, ∑ j : Fin n,
      2 * ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re
        = 2 * ‖overlap psi phi‖ ^ 2 := by
    have : ∀ i j : Fin n,
        ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i))
          = ((starRingEnd ℂ) (phi i) * psi i) * ((starRingEnd ℂ) (psi j) * phi j) := by
      intro i j; simp [map_mul]; ring
    calc ∑ i : Fin n, ∑ j : Fin n,
          2 * ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re
        = 2 * (∑ i : Fin n, ∑ j : Fin n,
            ((starRingEnd ℂ) (phi i) * psi i) * ((starRingEnd ℂ) (psi j) * phi j)).re := by
          simp only [Complex.re_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
            rw [this i j]))
      _ = 2 * (((starRingEnd ℂ) (overlap psi phi)) * (overlap psi phi)).re := by
          have hconj : (∑ i : Fin n, (starRingEnd ℂ) (phi i) * psi i)
              = (starRingEnd ℂ) (overlap psi phi) := by
            rw [overlap, map_sum]
            exact Finset.sum_congr rfl
              (fun i _ => by rw [map_mul, Complex.conj_conj]; ring)
          rw [← Finset.sum_mul_sum, hconj]
          rfl
      _ = 2 * ‖overlap psi phi‖ ^ 2 := by
          rw [Complex.sq_norm, ← Complex.normSq_eq_conj_mul_self]
          simp
  rw [acceptProb_eq_sum]
  simp only [hexp]
  simp only [Finset.sum_add_distrib]
  rw [h1, h2, hcross]
  ring

end QC

