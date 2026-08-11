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

/-!
# The SWAP test

We model the SWAP test circuit explicitly.  A pure state of a finite-dimensional
system with basis indexed by `ι` is a vector `psi : ι → ℂ` with `∑ i, ‖psi i‖ ^ 2 = 1`.

The circuit acts on one ancilla qubit together with two copies of the system,
i.e. on vectors indexed by `Fin 2 × ι × ι`:

* the input is `|0⟩ ⊗ |psi⟩ ⊗ |phi⟩`;
* a Hadamard gate is applied to the ancilla;
* a controlled-SWAP exchanges the two system registers when the ancilla is `1`;
* a Hadamard gate is applied to the ancilla again;
* the ancilla is measured, and the test *accepts* when the outcome is `0`.

The main result `QC.swap_test_overlap` states that the acceptance probability is
`(1 + |⟨psi|phi⟩| ^ 2) / 2`.
-/

namespace QC

variable {ι : Type*} [Fintype ι]

/-- The Hermitian inner product `⟨psi|phi⟩ = ∑ i, conj (psi i) * phi i`. -/
noncomputable def overlap (psi phi : ι → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (psi i) * phi i

/-- Hadamard gate acting on the ancilla qubit. -/
noncomputable def hadAncilla (v : Fin 2 × ι × ι → ℂ) : Fin 2 × ι × ι → ℂ :=
  fun p => (v (0, p.2) + (if p.1 = 0 then 1 else -1) * v (1, p.2)) / (Real.sqrt 2 : ℝ)

/-- Controlled-SWAP: swaps the two system registers exactly when the ancilla is `1`. -/
def cswap (v : Fin 2 × ι × ι → ℂ) : Fin 2 × ι × ι → ℂ :=
  fun p => if p.1 = 0 then v (0, p.2.1, p.2.2) else v (1, p.2.2, p.2.1)

/-- The input state `|0⟩ ⊗ |psi⟩ ⊗ |phi⟩`. -/
def initState (psi phi : ι → ℂ) : Fin 2 × ι × ι → ℂ :=
  fun p => if p.1 = 0 then psi p.2.1 * phi p.2.2 else 0

/-- The state of the three registers just before the measurement of the ancilla. -/
noncomputable def swapTestFinal (psi phi : ι → ℂ) : Fin 2 × ι × ι → ℂ :=
  hadAncilla (cswap (hadAncilla (initState psi phi)))

/-- The probability that the SWAP test accepts, i.e. that the ancilla is measured in
state `|0⟩`. -/
noncomputable def acceptProb (psi phi : ι → ℂ) : ℝ :=
  ∑ i, ∑ j, ‖swapTestFinal psi phi (0, i, j)‖ ^ 2

lemma sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this

omit [Fintype ι] in
/-- Explicit form of the amplitudes on the accepting branch of the SWAP test. -/
lemma swapTestFinal_zero (psi phi : ι → ℂ) (i j : ι) :
    swapTestFinal psi phi (0, i, j) = (psi i * phi j + psi j * phi i) / 2 := by
  simp only [swapTestFinal, hadAncilla, cswap, initState]
  norm_num
  field_simp
  ring_nf
  rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 from by rw [pow_two]; exact sqrt_two_sq]

lemma sum_normSq_mul (psi phi : ι → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) (hphi : ∑ i, ‖phi i‖ ^ 2 = 1) :
    ∑ i, ∑ j, Complex.normSq (psi i * phi j) = 1 := by
  have h : ∑ i, ∑ j, Complex.normSq (psi i * phi j)
      = (∑ i, Complex.normSq (psi i)) * ∑ j, Complex.normSq (phi j) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Complex.normSq_mul _ _
  rw [h]
  simp only [Complex.normSq_eq_norm_sq]
  rw [hpsi, hphi, one_mul]

lemma sum_cross (psi phi : ι → ℂ) :
    ∑ i, ∑ j, ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re = ‖overlap psi phi‖ ^ 2 := by
  have key : ∑ i, ∑ j, ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i))
      = (starRingEnd ℂ) (overlap psi phi) * overlap psi phi := by
    have h1 : (starRingEnd ℂ) (overlap psi phi) = ∑ i, psi i * (starRingEnd ℂ) (phi i) := by
      simp only [overlap, map_sum, map_mul, Complex.conj_conj]
    rw [h1, overlap, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul]
    ring
  calc ∑ i, ∑ j, ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re
      = (∑ i, ∑ j, ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i))).re := by
        simp [Complex.re_sum]
    _ = ‖overlap psi phi‖ ^ 2 := by
        rw [key, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.ofReal_re]

/-- **The SWAP test.**  If `psi` and `phi` are unit vectors, the SWAP test accepts with
probability `(1 + |⟨psi|phi⟩| ^ 2) / 2`. -/
theorem swap_test_overlap (psi phi : ι → ℂ)
    (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) (hphi : ∑ i, ‖phi i‖ ^ 2 = 1) :
    acceptProb psi phi = (1 + ‖overlap psi phi‖ ^ 2) / 2 := by
  have hexp : ∀ i j : ι, ‖swapTestFinal psi phi (0, i, j)‖ ^ 2
      = (Complex.normSq (psi i * phi j) + Complex.normSq (psi j * phi i)
          + 2 * ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re) / 4 := by
    intro i j
    rw [swapTestFinal_zero, ← Complex.normSq_eq_norm_sq]
    rw [show ((psi i * phi j + psi j * phi i) / 2 : ℂ) = (psi i * phi j + psi j * phi i) * (2:ℂ)⁻¹ by ring]
    rw [Complex.normSq_mul, Complex.normSq_add]
    simp [Complex.normSq_apply]
    ring
  simp only [acceptProb, hexp]
  rw [show ∀ (f : ι → ι → ℝ), (∑ i, ∑ j, (f i j) / 4) = (∑ i, ∑ j, f i j) / 4 from by
      intro f; simp [Finset.sum_div]]
  have h1 : ∑ i, ∑ j, (Complex.normSq (psi i * phi j) + Complex.normSq (psi j * phi i)
      + 2 * ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re)
      = (∑ i, ∑ j, Complex.normSq (psi i * phi j))
        + (∑ i, ∑ j, Complex.normSq (psi j * phi i))
        + 2 * ∑ i, ∑ j, ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [h1, sum_normSq_mul psi phi hpsi hphi, sum_cross psi phi]
  have h2 : ∑ i, ∑ j, Complex.normSq (psi j * phi i) = 1 := by
    rw [Finset.sum_comm]
    exact sum_normSq_mul psi phi hpsi hphi
  rw [h2]
  ring

/-- The probability that the SWAP test rejects, i.e. that the ancilla is measured in
state `|1⟩`. -/
noncomputable def rejectProb (psi phi : ι → ℂ) : ℝ :=
  ∑ i, ∑ j, ‖swapTestFinal psi phi (1, i, j)‖ ^ 2

omit [Fintype ι] in
/-- Explicit form of the amplitudes on the rejecting branch of the SWAP test. -/
lemma swapTestFinal_one (psi phi : ι → ℂ) (i j : ι) :
    swapTestFinal psi phi (1, i, j) = (psi i * phi j - psi j * phi i) / 2 := by
  simp only [swapTestFinal, hadAncilla, cswap, initState]
  norm_num
  field_simp
  ring_nf
  rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 from by rw [pow_two]; exact sqrt_two_sq]

/-- The SWAP test rejects with probability `(1 - |⟨psi|phi⟩| ^ 2) / 2`. -/
theorem swap_test_reject (psi phi : ι → ℂ)
    (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) (hphi : ∑ i, ‖phi i‖ ^ 2 = 1) :
    rejectProb psi phi = (1 - ‖overlap psi phi‖ ^ 2) / 2 := by
  have hexp : ∀ i j : ι, ‖swapTestFinal psi phi (1, i, j)‖ ^ 2
      = (Complex.normSq (psi i * phi j) + Complex.normSq (psi j * phi i)
          - 2 * ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re) / 4 := by
    intro i j
    rw [swapTestFinal_one, ← Complex.normSq_eq_norm_sq]
    rw [show ((psi i * phi j - psi j * phi i) / 2 : ℂ)
        = (psi i * phi j - psi j * phi i) * (2:ℂ)⁻¹ by ring]
    rw [Complex.normSq_mul, Complex.normSq_sub]
    simp [Complex.normSq_apply]
    ring
  simp only [rejectProb, hexp]
  rw [show ∀ (f : ι → ι → ℝ), (∑ i, ∑ j, (f i j) / 4) = (∑ i, ∑ j, f i j) / 4 from by
      intro f; simp [Finset.sum_div]]
  have h1 : ∑ i, ∑ j, (Complex.normSq (psi i * phi j) + Complex.normSq (psi j * phi i)
      - 2 * ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re)
      = (∑ i, ∑ j, Complex.normSq (psi i * phi j))
        + (∑ i, ∑ j, Complex.normSq (psi j * phi i))
        - 2 * ∑ i, ∑ j, ((psi i * phi j) * (starRingEnd ℂ) (psi j * phi i)).re := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [h1, sum_normSq_mul psi phi hpsi hphi, sum_cross psi phi]
  have h2 : ∑ i, ∑ j, Complex.normSq (psi j * phi i) = 1 := by
    rw [Finset.sum_comm]
    exact sum_normSq_mul psi phi hpsi hphi
  rw [h2]
  ring

/-- Sanity check: the two measurement outcomes of the SWAP test have total probability `1`. -/
theorem swap_test_total (psi phi : ι → ℂ)
    (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) (hphi : ∑ i, ‖phi i‖ ^ 2 = 1) :
    acceptProb psi phi + rejectProb psi phi = 1 := by
  rw [swap_test_overlap psi phi hpsi hphi, swap_test_reject psi phi hpsi hphi]
  ring

/-- Two identical unit states are always accepted by the SWAP test. -/
theorem swap_test_self (psi : ι → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) :
    acceptProb psi psi = 1 := by
  have hov : overlap psi psi = 1 := by
    have : overlap psi psi = ((∑ i, ‖psi i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [overlap, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, mul_comm]
    rw [this, hpsi]
    norm_num
  rw [swap_test_overlap psi psi hpsi hpsi, hov]
  norm_num

end QC

