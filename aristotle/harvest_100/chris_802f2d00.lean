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

import Mathlib
/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate Finset

namespace QC

variable {n : ℕ}

/-- A pure state of an `n`-level quantum register. -/
abbrev Reg (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- A state of the full swap-test system: one ancilla qubit together with two
`n`-level registers.  We record it as its amplitude function. -/
abbrev SysState (n : ℕ) := Fin 2 × (Fin n × Fin n) → ℂ

/-- The Hadamard gate acting on the ancilla qubit. -/
noncomputable def hadAncilla (v : SysState n) : SysState n := fun p =>
  if p.1 = 0 then (v (0, p.2) + v (1, p.2)) / (Real.sqrt 2 : ℂ)
  else (v (0, p.2) - v (1, p.2)) / (Real.sqrt 2 : ℂ)

/-- The controlled-SWAP (Fredkin) gate: it swaps the two registers exactly when the
ancilla is in state `|1⟩`. -/
def cswap (v : SysState n) : SysState n := fun p =>
  if p.1 = 0 then v (0, p.2) else v (1, (p.2.2, p.2.1))

/-- The input state `|0⟩ ⊗ ψ ⊗ φ` of the swap test. -/
def initState (ψ φ : Reg n) : SysState n := fun p =>
  if p.1 = 0 then ψ.ofLp p.2.1 * φ.ofLp p.2.2 else 0

/-- The state produced by the swap-test circuit `H · CSWAP · H` applied to `|0⟩ ⊗ ψ ⊗ φ`. -/
noncomputable def swapTestFinal (ψ φ : Reg n) : SysState n :=
  hadAncilla (cswap (hadAncilla (initState ψ φ)))

/-- The probability that the swap test *accepts*, i.e. that the final measurement of the
ancilla qubit returns `0`. -/
noncomputable def acceptProb (ψ φ : Reg n) : ℝ :=
  ∑ x : Fin n × Fin n, ‖swapTestFinal ψ φ (0, x)‖ ^ 2

/-- The probability that the swap test *rejects*, i.e. that the final measurement of the
ancilla qubit returns `1`. -/
noncomputable def rejectProb (ψ φ : Reg n) : ℝ :=
  ∑ x : Fin n × Fin n, ‖swapTestFinal ψ φ (1, x)‖ ^ 2

/-- The amplitudes of the accepted branch are the symmetrised products. -/
lemma swapTestFinal_zero (ψ φ : Reg n) (x : Fin n × Fin n) :
    swapTestFinal ψ φ (0, x) =
      (ψ.ofLp x.1 * φ.ofLp x.2 + ψ.ofLp x.2 * φ.ofLp x.1) / 2 := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  simp only [swapTestFinal, hadAncilla, cswap, initState]
  norm_num
  rw [← add_div, div_div, hsq]

/-- The amplitudes of the rejected branch are the antisymmetrised products. -/
lemma swapTestFinal_one (ψ φ : Reg n) (x : Fin n × Fin n) :
    swapTestFinal ψ φ (1, x) =
      (ψ.ofLp x.1 * φ.ofLp x.2 - ψ.ofLp x.2 * φ.ofLp x.1) / 2 := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  simp only [swapTestFinal, hadAncilla, cswap, initState]
  norm_num
  rw [← sub_div, div_div, hsq]

/-- Unit vectors satisfy `∑ i, ψ i * conj (ψ i) = 1`. -/
lemma sum_mul_conj_self (ψ : Reg n) (h : ‖ψ‖ = 1) :
    ∑ i, ψ.ofLp i * conj (ψ.ofLp i) = 1 := by
  have h1 : (inner ℂ ψ ψ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, h]; norm_num
  rw [PiLp.inner_apply] at h1
  simp only [RCLike.inner_apply] at h1
  rw [← h1]

/-- The inner product as an explicit sum. -/
lemma inner_eq_sum (ψ φ : Reg n) :
    (inner ℂ ψ φ : ℂ) = ∑ i, conj (ψ.ofLp i) * φ.ofLp i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The core algebraic identity behind the swap test. -/
lemma sum_symmetrised (ψ φ : Reg n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ∑ x : Fin n × Fin n,
      (ψ.ofLp x.1 * φ.ofLp x.2 + ψ.ofLp x.2 * φ.ofLp x.1) *
        conj (ψ.ofLp x.1 * φ.ofLp x.2 + ψ.ofLp x.2 * φ.ofLp x.1)
      = 2 + 2 * ((inner ℂ ψ φ : ℂ) * conj (inner ℂ ψ φ : ℂ)) := by
  have hc := inner_eq_sum ψ φ
  have hcc : conj (inner ℂ ψ φ : ℂ) = ∑ i, ψ.ofLp i * conj (φ.ofLp i) := by
    rw [hc, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, Complex.conj_conj, mul_comm]
  have expand : ∀ i j : Fin n,
      (ψ.ofLp i * φ.ofLp j + ψ.ofLp j * φ.ofLp i) *
        conj (ψ.ofLp i * φ.ofLp j + ψ.ofLp j * φ.ofLp i)
      = (ψ.ofLp i * conj (ψ.ofLp i)) * (φ.ofLp j * conj (φ.ofLp j))
        + (ψ.ofLp i * conj (φ.ofLp i)) * (conj (ψ.ofLp j) * φ.ofLp j)
        + (conj (ψ.ofLp i) * φ.ofLp i) * (ψ.ofLp j * conj (φ.ofLp j))
        + (φ.ofLp i * conj (φ.ofLp i)) * (ψ.ofLp j * conj (ψ.ofLp j)) := by
    intro i j
    simp only [map_add, map_mul]
    ring
  rw [Fintype.sum_prod_type]
  simp only [expand, Finset.sum_add_distrib, ← Finset.sum_mul_sum]
  rw [sum_mul_conj_self ψ hψ, sum_mul_conj_self φ hφ, ← hc, ← hcc]
  ring

/-- The companion identity for the rejected branch. -/
lemma sum_antisymmetrised (ψ φ : Reg n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ∑ x : Fin n × Fin n,
      (ψ.ofLp x.1 * φ.ofLp x.2 - ψ.ofLp x.2 * φ.ofLp x.1) *
        conj (ψ.ofLp x.1 * φ.ofLp x.2 - ψ.ofLp x.2 * φ.ofLp x.1)
      = 2 - 2 * ((inner ℂ ψ φ : ℂ) * conj (inner ℂ ψ φ : ℂ)) := by
  have hc := inner_eq_sum ψ φ
  have hcc : conj (inner ℂ ψ φ : ℂ) = ∑ i, ψ.ofLp i * conj (φ.ofLp i) := by
    rw [hc, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, Complex.conj_conj, mul_comm]
  have expand : ∀ i j : Fin n,
      (ψ.ofLp i * φ.ofLp j - ψ.ofLp j * φ.ofLp i) *
        conj (ψ.ofLp i * φ.ofLp j - ψ.ofLp j * φ.ofLp i)
      = (ψ.ofLp i * conj (ψ.ofLp i)) * (φ.ofLp j * conj (φ.ofLp j))
        + (ψ.ofLp i * conj (φ.ofLp i)) * (-(conj (ψ.ofLp j) * φ.ofLp j))
        + (conj (ψ.ofLp i) * φ.ofLp i) * (-(ψ.ofLp j * conj (φ.ofLp j)))
        + (φ.ofLp i * conj (φ.ofLp i)) * (ψ.ofLp j * conj (ψ.ofLp j)) := by
    intro i j
    simp only [map_sub, map_mul]
    ring
  rw [Fintype.sum_prod_type]
  simp only [expand, Finset.sum_add_distrib, ← Finset.sum_mul_sum, Finset.sum_neg_distrib]
  rw [sum_mul_conj_self ψ hψ, sum_mul_conj_self φ hφ, ← hc, ← hcc]
  ring

/-- **Swap test.** For unit vectors `ψ` and `φ`, the swap test accepts (the ancilla is
measured to be `0`) with probability `(1 + |⟨ψ, φ⟩|²)/2`. -/
theorem swap_test_overlap (ψ φ : Reg n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    acceptProb ψ φ = (1 + ‖(inner ℂ ψ φ : ℂ)‖ ^ 2) / 2 := by
  have key := sum_symmetrised ψ φ hψ hφ
  have hnorm : ((‖(inner ℂ ψ φ : ℂ)‖ ^ 2 : ℝ) : ℂ)
      = (inner ℂ ψ φ : ℂ) * conj (inner ℂ ψ φ : ℂ) := by
    rw [Complex.sq_norm, Complex.mul_conj]
  have hterm : ∀ x : Fin n × Fin n, ((‖swapTestFinal ψ φ (0, x)‖ ^ 2 : ℝ) : ℂ)
      = ((ψ.ofLp x.1 * φ.ofLp x.2 + ψ.ofLp x.2 * φ.ofLp x.1) *
          conj (ψ.ofLp x.1 * φ.ofLp x.2 + ψ.ofLp x.2 * φ.ofLp x.1)) / 4 := by
    intro x
    rw [Complex.sq_norm, ← Complex.mul_conj, swapTestFinal_zero, map_div₀]
    simp only [map_ofNat]
    ring
  have hreal : ((acceptProb ψ φ : ℝ) : ℂ) = (((1 + ‖(inner ℂ ψ φ : ℂ)‖ ^ 2) / 2 : ℝ) : ℂ) := by
    rw [acceptProb, Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_one, hnorm, Finset.sum_congr rfl fun x _ => hterm x,
      ← Finset.sum_div, key]
    simp only [Complex.ofReal_ofNat]
    ring
  exact_mod_cast hreal

/-- The swap test rejects with probability `(1 - |⟨ψ, φ⟩|²)/2`. -/
theorem swap_test_reject (ψ φ : Reg n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    rejectProb ψ φ = (1 - ‖(inner ℂ ψ φ : ℂ)‖ ^ 2) / 2 := by
  have key := sum_antisymmetrised ψ φ hψ hφ
  have hnorm : ((‖(inner ℂ ψ φ : ℂ)‖ ^ 2 : ℝ) : ℂ)
      = (inner ℂ ψ φ : ℂ) * conj (inner ℂ ψ φ : ℂ) := by
    rw [Complex.sq_norm, Complex.mul_conj]
  have hterm : ∀ x : Fin n × Fin n, ((‖swapTestFinal ψ φ (1, x)‖ ^ 2 : ℝ) : ℂ)
      = ((ψ.ofLp x.1 * φ.ofLp x.2 - ψ.ofLp x.2 * φ.ofLp x.1) *
          conj (ψ.ofLp x.1 * φ.ofLp x.2 - ψ.ofLp x.2 * φ.ofLp x.1)) / 4 := by
    intro x
    rw [Complex.sq_norm, ← Complex.mul_conj, swapTestFinal_one, map_div₀]
    simp only [map_ofNat]
    ring
  have hreal : ((rejectProb ψ φ : ℝ) : ℂ) = (((1 - ‖(inner ℂ ψ φ : ℂ)‖ ^ 2) / 2 : ℝ) : ℂ) := by
    rw [rejectProb, Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_one, hnorm, Finset.sum_congr rfl fun x _ => hterm x,
      ← Finset.sum_div, key]
    simp only [Complex.ofReal_ofNat]
    ring
  exact_mod_cast hreal

/-- The two outcomes of the swap test form a probability distribution. -/
theorem acceptProb_add_rejectProb (ψ φ : Reg n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    acceptProb ψ φ + rejectProb ψ φ = 1 := by
  rw [swap_test_overlap ψ φ hψ hφ, swap_test_reject ψ φ hψ hφ]
  ring

/-- Identical unit states are always accepted. -/
theorem acceptProb_self (ψ : Reg n) (hψ : ‖ψ‖ = 1) : acceptProb ψ ψ = 1 := by
  rw [swap_test_overlap ψ ψ hψ hψ, inner_self_eq_norm_sq_to_K, hψ]
  norm_num

/-- Orthogonal unit states are accepted with probability `1/2`. -/
theorem acceptProb_orthogonal (ψ φ : Reg n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (h : (inner ℂ ψ φ : ℂ) = 0) : acceptProb ψ φ = 1 / 2 := by
  rw [swap_test_overlap ψ φ hψ hφ, h]
  norm_num

end QC

