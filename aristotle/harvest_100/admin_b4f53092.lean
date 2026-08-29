/-
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open ComplexConjugate

namespace QC

variable {n : Type*} [Fintype n]

/-- The overlap `⟨ψ|φ⟩` of two state vectors indexed by `n`. -/
noncomputable def overlap (psi phi : n → ℂ) : ℂ := ∑ i, conj (psi i) * phi i

/-- A state vector is normalized when the sum of the squared moduli of its
amplitudes is `1`. -/
def IsNormalized (psi : n → ℂ) : Prop := ∑ i, ‖psi i‖ ^ 2 = 1

/-- The initial state of the SWAP-test circuit: an ancilla qubit in `|0⟩`
(indexed by `false`) together with the two registers in state `|ψ⟩ ⊗ |φ⟩`. -/
noncomputable def initState (psi phi : n → ℂ) : Bool × n × n → ℂ :=
  fun p => if p.1 then 0 else psi p.2.1 * phi p.2.2

/-- Hadamard gate acting on the ancilla qubit. -/
noncomputable def hadamardAncilla (f : Bool × n × n → ℂ) : Bool × n × n → ℂ :=
  fun p => if p.1 then (f (false, p.2) - f (true, p.2)) / (Real.sqrt 2 : ℂ)
           else (f (false, p.2) + f (true, p.2)) / (Real.sqrt 2 : ℂ)

/-- Controlled-SWAP: when the ancilla is `|1⟩` the two registers are swapped. -/
noncomputable def cswap (f : Bool × n × n → ℂ) : Bool × n × n → ℂ :=
  fun p => if p.1 then f (true, p.2.2, p.2.1) else f (false, p.2.1, p.2.2)

/-- The full SWAP-test circuit: Hadamard, controlled-SWAP, Hadamard. -/
noncomputable def swapTestState (psi phi : n → ℂ) : Bool × n × n → ℂ :=
  hadamardAncilla (cswap (hadamardAncilla (initState psi phi)))

/-- The SWAP test *accepts* when the ancilla is measured in `|0⟩`; this is the
corresponding probability. -/
noncomputable def acceptProb (psi phi : n → ℂ) : ℝ :=
  ∑ i, ∑ j, ‖swapTestState psi phi (false, i, j)‖ ^ 2

omit [Fintype n] in
/-- The amplitude of the accepting branch of the SWAP test is
`(ψ_i φ_j + φ_i ψ_j) / 2`. -/
theorem swapTestState_false (psi phi : n → ℂ) (i j : n) :
    swapTestState psi phi (false, i, j) = (psi i * phi j + phi i * psi j) / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp
  simp only [swapTestState, hadamardAncilla, cswap, initState, if_true, if_false,
    Bool.false_eq_true]
  field_simp
  ring_nf
  rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 by rw [sq]; exact h2]

/-- **SWAP test.** For normalized states `ψ` and `φ`, the SWAP test accepts with
probability `(1 + |⟨ψ|φ⟩|²) / 2`. -/
theorem swap_test_overlap (psi phi : n → ℂ)
    (hpsi : IsNormalized psi) (hphi : IsNormalized phi) :
    acceptProb psi phi = (1 + ‖overlap psi phi‖ ^ 2) / 2 := by
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = conj z * z := by
    intro z
    simp [Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_norm_sq]
  have hpsi' : ∑ i, conj (psi i) * psi i = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hpsi
    simpa [hz] using this
  have hphi' : ∑ i, conj (phi i) * phi i = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hphi
    simpa [hz] using this
  apply Complex.ofReal_injective
  have hexp : ∀ i j : n,
      ((‖swapTestState psi phi (false, i, j)‖ ^ 2 : ℝ) : ℂ) =
        ((conj (psi i) * psi i) * (conj (phi j) * phi j)
          + (conj (psi i) * phi i) * (conj (phi j) * psi j)
          + (conj (phi i) * psi i) * (conj (psi j) * phi j)
          + (conj (phi i) * phi i) * (conj (psi j) * psi j)) / 4 := by
    intro i j
    rw [hz, swapTestState_false]
    simp only [map_div₀, map_add, map_mul, Complex.conj_ofNat]
    ring
  calc ((acceptProb psi phi : ℝ) : ℂ)
      = ∑ i, ∑ j, ((‖swapTestState psi phi (false, i, j)‖ ^ 2 : ℝ) : ℂ) := by
        simp only [acceptProb]
        push_cast
        ring
    _ = (1 + conj (overlap psi phi) * overlap psi phi) / 2 := by
        simp only [hexp]
        simp only [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
        rw [hpsi', hphi']
        have hc : conj (overlap psi phi) = ∑ i, conj (phi i) * psi i := by
          simp only [overlap, map_sum, map_mul, Complex.conj_conj]
          exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
        rw [hc]
        simp only [overlap]
        ring
    _ = ((((1 + ‖overlap psi phi‖ ^ 2) / 2 : ℝ)) : ℂ) := by
        push_cast [hz]
        ring

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

