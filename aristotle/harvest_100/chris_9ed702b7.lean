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

import Mathlib

open scoped ComplexConjugate

namespace QC

variable {n : ℕ}

/-- The product state `ψ ⊗ φ` of two `n`-level registers, as a vector indexed by
pairs of basis labels. -/
noncomputable def tensor (ψ φ : EuclideanSpace ℂ (Fin n)) : Fin n × Fin n → ℂ :=
  fun p => ψ p.1 * φ p.2

/-- A state of the whole swap-test register: one ancilla qubit (`Fin 2`) together
with the two `n`-level registers. -/
abbrev State (n : ℕ) := Fin 2 × (Fin n × Fin n) → ℂ

/-- The Hadamard gate acting on the ancilla qubit:
`|0⟩ ↦ (|0⟩+|1⟩)/√2`, `|1⟩ ↦ (|0⟩-|1⟩)/√2`. -/
noncomputable def hadamardAncilla (f : State n) : State n :=
  fun q =>
    if q.1 = 0 then (f (0, q.2) + f (1, q.2)) / (Real.sqrt 2 : ℂ)
    else (f (0, q.2) - f (1, q.2)) / (Real.sqrt 2 : ℂ)

/-- The controlled-SWAP gate: it exchanges the two registers exactly when the
ancilla qubit is `1`. -/
noncomputable def cswap (f : State n) : State n :=
  fun q => if q.1 = 0 then f (0, q.2) else f (1, q.2.swap)

/-- The initial state of the swap test: ancilla in `|0⟩`, registers in `ψ ⊗ φ`. -/
noncomputable def initState (ψ φ : EuclideanSpace ℂ (Fin n)) : State n :=
  fun q => if q.1 = 0 then tensor ψ φ q.2 else 0

/-- The state at the end of the swap-test circuit: Hadamard on the ancilla,
controlled-SWAP, Hadamard on the ancilla. -/
noncomputable def swapTestFinal (ψ φ : EuclideanSpace ℂ (Fin n)) : State n :=
  hadamardAncilla (cswap (hadamardAncilla (initState ψ φ)))

/-- The probability that the swap test accepts, i.e. that measuring the ancilla in
the computational basis yields `0`. -/
noncomputable def acceptProb (ψ φ : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ∑ x : Fin n × Fin n, ‖swapTestFinal ψ φ (0, x)‖ ^ 2

/-- The probability that the swap test rejects, i.e. that measuring the ancilla in
the computational basis yields `1`. -/
noncomputable def rejectProb (ψ φ : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ∑ x : Fin n × Fin n, ‖swapTestFinal ψ φ (1, x)‖ ^ 2

section Amplitudes

private lemma sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

private lemma sqrt_two_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  simp

/-- The amplitude of the accepting branch is the symmetrized product state. -/
lemma swapTestFinal_zero (ψ φ : EuclideanSpace ℂ (Fin n)) (x : Fin n × Fin n) :
    swapTestFinal ψ φ (0, x) = (ψ x.1 * φ x.2 + 1 * (φ x.1 * ψ x.2)) / 2 := by
  have hne := sqrt_two_ne_zero
  simp only [swapTestFinal, hadamardAncilla, cswap, initState, tensor]
  norm_num [Prod.swap]
  field_simp
  rw [sqrt_two_sq]
  ring

/-- The amplitude of the rejecting branch is the antisymmetrized product state. -/
lemma swapTestFinal_one (ψ φ : EuclideanSpace ℂ (Fin n)) (x : Fin n × Fin n) :
    swapTestFinal ψ φ (1, x) = (ψ x.1 * φ x.2 + (-1) * (φ x.1 * ψ x.2)) / 2 := by
  have hne := sqrt_two_ne_zero
  simp only [swapTestFinal, hadamardAncilla, cswap, initState, tensor]
  norm_num [Prod.swap]
  field_simp
  rw [sqrt_two_sq]
  ring

end Amplitudes

/-- For a unit vector the amplitudes have squared moduli summing to one. -/
lemma sum_mul_conj_of_norm_one (ψ : EuclideanSpace ℂ (Fin n)) (h : ‖ψ‖ = 1) :
    ∑ i, ψ i * conj (ψ i) = 1 := by
  have h2 : ∑ i, ‖ψ i‖ ^ 2 = 1 := by
    have hn := EuclideanSpace.norm_eq ψ
    rw [h, eq_comm, Real.sqrt_eq_one] at hn
    exact hn
  have h3 : ∑ i, ψ i * conj (ψ i) = ∑ i, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj']
    push_cast; ring
  rw [h3, ← Complex.ofReal_sum, h2, Complex.ofReal_one]

/-- The overlap `⟨ψ|φ⟩` written as an explicit sum. -/
lemma inner_eq_sum (ψ φ : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ ψ φ : ℂ) = ∑ i, conj (ψ i) * φ i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The key computation: for unit vectors `ψ`, `φ` and any coefficient `c`, the
squared norm of the (unnormalized) branch `ψ ⊗ φ + c • (φ ⊗ ψ)`. -/
lemma sum_branch_sq (ψ φ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (c : ℂ) :
    ∑ x : Fin n × Fin n,
        (ψ x.1 * φ x.2 + c * (φ x.1 * ψ x.2)) * conj (ψ x.1 * φ x.2 + c * (φ x.1 * ψ x.2))
      = 1 + c * conj c
        + (c + conj c) * ((inner ℂ ψ φ : ℂ) * conj (inner ℂ ψ φ : ℂ)) := by
  have rank_one_double_sum : ∀ f1 g1 f2 g2 f3 g3 f4 g4 : Fin n → ℂ,
      ∑ i, ∑ j, (f1 i * g1 j + f2 i * g2 j + f3 i * g3 j + f4 i * g4 j)
        = (∑ i, f1 i) * (∑ j, g1 j) + (∑ i, f2 i) * (∑ j, g2 j)
          + (∑ i, f3 i) * (∑ j, g3 j) + (∑ i, f4 i) * (∑ j, g4 j) := by
    intro f1 g1 f2 g2 f3 g3 f4 g4
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hA : ∑ i, ψ i * conj (ψ i) = 1 := sum_mul_conj_of_norm_one ψ hψ
  have hB : ∑ i, φ i * conj (φ i) = 1 := sum_mul_conj_of_norm_one φ hφ
  set S : ℂ := (inner ℂ ψ φ : ℂ) with hSdef
  have hS : S = ∑ i, φ i * conj (ψ i) := by
    rw [hSdef, inner_eq_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hSc : conj S = ∑ i, ψ i * conj (φ i) := by
    rw [hSdef, inner_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, Complex.conj_conj, mul_comm]
  have hterm : ∀ x : Fin n × Fin n,
      (ψ x.1 * φ x.2 + c * (φ x.1 * ψ x.2)) * conj (ψ x.1 * φ x.2 + c * (φ x.1 * ψ x.2))
        = (ψ x.1 * conj (ψ x.1)) * (φ x.2 * conj (φ x.2))
          + (ψ x.1 * conj (φ x.1)) * (conj c * (φ x.2 * conj (ψ x.2)))
          + (φ x.1 * conj (ψ x.1)) * (c * (ψ x.2 * conj (φ x.2)))
          + (φ x.1 * conj (φ x.1)) * ((c * conj c) * (ψ x.2 * conj (ψ x.2))) := by
    intro x
    simp only [map_add, map_mul]
    ring
  rw [Finset.sum_congr rfl fun x _ => hterm x, Fintype.sum_prod_type]
  dsimp only
  rw [rank_one_double_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    hA, hB, ← hS, ← hSc]
  ring

/-- Turning a complex-valued computation of `∑ ‖·‖²` into a real one. -/
private lemma ofReal_sum_norm_sq (g : Fin n × Fin n → ℂ) :
    ((∑ x : Fin n × Fin n, ‖g x‖ ^ 2 : ℝ) : ℂ) = ∑ x : Fin n × Fin n, g x * conj (g x) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [Complex.mul_conj']; push_cast; ring

/-- **Swap test.** For two unit vectors `ψ` and `φ`, the swap test
(Hadamard, controlled-SWAP, Hadamard, then measure the ancilla) accepts with
probability `(1 + |⟨ψ, φ⟩|²)/2`. -/
theorem swap_test_overlap (ψ φ : EuclideanSpace ℂ (Fin n))
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    acceptProb ψ φ = (1 + ‖(inner ℂ ψ φ : ℂ)‖ ^ 2) / 2 := by
  set S : ℂ := (inner ℂ ψ φ : ℂ) with hSdef
  have key : ((acceptProb ψ φ : ℝ) : ℂ) = ((( 1 + ‖S‖ ^ 2) / 2 : ℝ) : ℂ) := by
    rw [acceptProb, ofReal_sum_norm_sq]
    have hterm : ∀ x : Fin n × Fin n,
        swapTestFinal ψ φ (0, x) * conj (swapTestFinal ψ φ (0, x))
          = ((ψ x.1 * φ x.2 + 1 * (φ x.1 * ψ x.2))
              * conj (ψ x.1 * φ x.2 + 1 * (φ x.1 * ψ x.2))) / 4 := by
      intro x
      rw [swapTestFinal_zero]
      simp only [map_div₀, Complex.conj_ofNat]
      ring
    rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_div,
      sum_branch_sq ψ φ hψ hφ 1, ← hSdef, Complex.mul_conj' S]
    simp only [map_one]
    push_cast
    ring
  have hre := congrArg Complex.re key
  rwa [Complex.ofReal_re, Complex.ofReal_re] at hre

/-- The swap test rejects with probability `(1 - |⟨ψ, φ⟩|²)/2`; together with
`QC.swap_test_overlap` this shows the two outcome probabilities sum to `1`. -/
theorem swap_test_reject (ψ φ : EuclideanSpace ℂ (Fin n))
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    rejectProb ψ φ = (1 - ‖(inner ℂ ψ φ : ℂ)‖ ^ 2) / 2 := by
  set S : ℂ := (inner ℂ ψ φ : ℂ) with hSdef
  have key : ((rejectProb ψ φ : ℝ) : ℂ) = ((( 1 - ‖S‖ ^ 2) / 2 : ℝ) : ℂ) := by
    rw [rejectProb, ofReal_sum_norm_sq]
    have hterm : ∀ x : Fin n × Fin n,
        swapTestFinal ψ φ (1, x) * conj (swapTestFinal ψ φ (1, x))
          = ((ψ x.1 * φ x.2 + (-1) * (φ x.1 * ψ x.2))
              * conj (ψ x.1 * φ x.2 + (-1) * (φ x.1 * ψ x.2))) / 4 := by
      intro x
      rw [swapTestFinal_one]
      simp only [map_div₀, Complex.conj_ofNat]
      ring
    rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_div,
      sum_branch_sq ψ φ hψ hφ (-1), ← hSdef, Complex.mul_conj' S]
    simp only [map_neg, map_one]
    push_cast
    ring
  have hre := congrArg Complex.re key
  rwa [Complex.ofReal_re, Complex.ofReal_re] at hre

/-- Sanity check: the two outcome probabilities sum to one. -/
theorem accept_add_reject (ψ φ : EuclideanSpace ℂ (Fin n))
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    acceptProb ψ φ + rejectProb ψ φ = 1 := by
  rw [swap_test_overlap ψ φ hψ hφ, swap_test_reject ψ φ hψ hφ]
  ring

/-- Sanity check: identical states are always accepted. -/
theorem acceptProb_self (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) :
    acceptProb ψ ψ = 1 := by
  rw [swap_test_overlap ψ ψ hψ hψ, inner_self_eq_norm_sq_to_K, hψ]
  norm_num

end QC

