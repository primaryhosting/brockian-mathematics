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

set_option grind.warning false

open scoped ComplexConjugate

namespace QC

variable {d : ℕ}

/-- Index type for the three registers used in the SWAP test: a one-qubit
ancilla (`Fin 2`) together with two `d`-dimensional data registers.  A state of
the whole system is a complex amplitude function on this index type. -/
abbrev Reg (d : ℕ) : Type := Fin 2 × Fin d × Fin d

/-- The initial state of the SWAP test, `|0⟩ ⊗ |ψ⟩ ⊗ |ϕ⟩`. -/
noncomputable def initState (ψ ϕ : Fin d → ℂ) : Reg d → ℂ :=
  fun p => if p.1 = 0 then ψ p.2.1 * ϕ p.2.2 else 0

/-- The Hadamard gate acting on the ancilla qubit,
`|0⟩ ↦ (|0⟩+|1⟩)/√2` and `|1⟩ ↦ (|0⟩-|1⟩)/√2`.
On amplitudes this reads `w a = (v 0 + (-1)^a * v 1)/√2`. -/
noncomputable def hadamardAncilla (v : Reg d → ℂ) : Reg d → ℂ :=
  fun p => ((Real.sqrt 2)⁻¹ : ℝ) *
    (v (0, p.2) + (if p.1 = 0 then (1 : ℂ) else -1) * v (1, p.2))

/-- The controlled-SWAP (Fredkin) gate: when the ancilla is `|1⟩` the contents
of the two data registers are exchanged. -/
def cswap (v : Reg d → ℂ) : Reg d → ℂ :=
  fun p => if p.1 = 0 then v (0, p.2.1, p.2.2) else v (1, p.2.2, p.2.1)

/-- The state produced by the SWAP test circuit applied to `|0⟩|ψ⟩|ϕ⟩`:
Hadamard on the ancilla, then controlled swap, then Hadamard again. -/
noncomputable def swapTestState (ψ ϕ : Fin d → ℂ) : Reg d → ℂ :=
  hadamardAncilla (cswap (hadamardAncilla (initState ψ ϕ)))

/-- The SWAP test *accepts* when the final measurement of the ancilla yields
`0`; this is the probability of that outcome. -/
noncomputable def swapTestAcceptProb (ψ ϕ : Fin d → ℂ) : ℝ :=
  ∑ q : Fin d × Fin d, ‖swapTestState ψ ϕ (0, q)‖ ^ 2

/-- The amplitudes of the accepting branch of the SWAP test are
`(ψ i ϕ j + ψ j ϕ i)/2`, i.e. the branch carries the symmetrized state. -/
theorem swapTestState_zero (ψ ϕ : Fin d → ℂ) (i j : Fin d) :
    swapTestState ψ ϕ (0, i, j) = (2 : ℂ)⁻¹ * (ψ i * ϕ j + ψ j * ϕ i) := by
  have h2 : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = (2 : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  simp only [swapTestState, hadamardAncilla, cswap, initState]
  norm_num
  linear_combination (ψ i * ϕ j + ψ j * ϕ i) * h2

/-- The amplitudes of the rejecting branch of the SWAP test are
`(ψ i ϕ j - ψ j ϕ i)/2`, i.e. the branch carries the antisymmetrized state. -/
theorem swapTestState_one (ψ ϕ : Fin d → ℂ) (i j : Fin d) :
    swapTestState ψ ϕ (1, i, j) = (2 : ℂ)⁻¹ * (ψ i * ϕ j - ψ j * ϕ i) := by
  have h2 : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = (2 : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  simp only [swapTestState, hadamardAncilla, cswap, initState]
  norm_num
  linear_combination (ψ i * ϕ j - ψ j * ϕ i) * h2

/-- Casting the squared norm of a complex number: `‖z‖² = z * conj z`. -/
private theorem ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj]
  norm_cast
  exact Complex.sq_norm z

/-- Expansion of the double sum occurring in the acceptance probability. -/
private theorem sum_expand (ψ ϕ : Fin d → ℂ) :
    ∑ i, ∑ j, (ψ i * ϕ j + ψ j * ϕ i) *
        (conj (ψ i) * conj (ϕ j) + conj (ψ j) * conj (ϕ i))
      = 2 * ((∑ i, ψ i * conj (ψ i)) * (∑ j, ϕ j * conj (ϕ j)))
        + 2 * ((∑ i, ψ i * conj (ϕ i)) * (∑ j, ϕ j * conj (ψ j))) := by
  have h1 : ∀ f g : Fin d → ℂ, ∑ i, ∑ j, f i * g j = (∑ i, f i) * (∑ j, g j) := by
    intro f g; rw [Finset.sum_mul_sum]
  have h2 : ∀ f g : Fin d → ℂ, ∑ i, ∑ j, f j * g i = (∑ j, f j) * (∑ i, g i) := by
    intro f g; rw [Finset.sum_comm, Finset.sum_mul_sum]
  have e : ∀ i j : Fin d,
      (ψ i * ϕ j + ψ j * ϕ i) * (conj (ψ i) * conj (ϕ j) + conj (ψ j) * conj (ϕ i))
        = (ψ i * conj (ψ i)) * (ϕ j * conj (ϕ j)) + (ψ i * conj (ϕ i)) * (ϕ j * conj (ψ j))
          + (ψ j * conj (ψ j)) * (ϕ i * conj (ϕ i))
          + (ψ j * conj (ϕ j)) * (ϕ i * conj (ψ i)) := by
    intro i j; ring
  simp only [e, Finset.sum_add_distrib, h1, h2]
  ring

/-- A unit vector of `EuclideanSpace ℂ (Fin d)` has `∑ i, ψ i * conj (ψ i) = 1`. -/
private theorem sum_mul_conj_self_of_norm_one (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1) :
    ∑ i, ψ i * conj (ψ i) = (1 : ℂ) := by
  have hsum : ∑ i, ‖ψ i‖ ^ 2 = (1 : ℝ) := by
    have h := EuclideanSpace.norm_eq ψ
    rw [hψ] at h
    have h' := congrArg (fun t => t ^ 2) h
    simp only at h'
    rw [Real.sq_sqrt (by positivity)] at h'
    linarith [h']
  calc ∑ i, ψ i * conj (ψ i) = ∑ i, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun i _ => (ofReal_norm_sq (ψ i)).symm
    _ = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    _ = 1 := by rw [hsum]; norm_num

/-- **The SWAP test.**  For unit vectors `ψ` and `ϕ`, the SWAP test on
`|0⟩|ψ⟩|ϕ⟩` accepts (measures `0` on the ancilla) with probability
`(1 + |⟨ψ|ϕ⟩|²)/2`. -/
theorem swap_test_overlap (ψ ϕ : EuclideanSpace ℂ (Fin d))
    (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    swapTestAcceptProb (WithLp.ofLp ψ) (WithLp.ofLp ϕ)
      = (1 + ‖(inner ℂ ψ ϕ : ℂ)‖ ^ 2) / 2 := by
  have hinner : (inner ℂ ψ ϕ : ℂ) = ∑ i, conj (ψ i) * ϕ i := by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hψ1 : ∑ i, ψ i * conj (ψ i) = (1 : ℂ) := sum_mul_conj_self_of_norm_one ψ hψ
  have hϕ1 : ∑ i, ϕ i * conj (ϕ i) = (1 : ℂ) := sum_mul_conj_self_of_norm_one ϕ hϕ
  -- the overlap, written as `A = ∑ ψ i * conj (ϕ i)`
  set A : ℂ := ∑ i, ψ i * conj (ϕ i) with hA
  have hAc : ∑ i, ϕ i * conj (ψ i) = conj A := by
    rw [hA, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, Complex.conj_conj, mul_comm]
  have hnorm : ((‖(inner ℂ ψ ϕ : ℂ)‖ ^ 2 : ℝ) : ℂ) = A * conj A := by
    rw [ofReal_norm_sq, hinner]
    have : ∑ i, conj (ψ i) * ϕ i = conj A := by
      rw [hA, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, Complex.conj_conj, mul_comm]
    rw [this, Complex.conj_conj]
    ring
  have hcast : ∀ z : ℂ, ((‖z‖ : ℂ)) ^ 2 = z * conj z := by
    intro z
    rw [← Complex.ofReal_pow]
    exact ofReal_norm_sq z
  have hnorm' : ((‖(inner ℂ ψ ϕ : ℂ)‖ : ℂ)) ^ 2 = A * conj A := by
    rw [← Complex.ofReal_pow]; exact hnorm
  refine Complex.ofReal_inj.mp ?_
  rw [swapTestAcceptProb]
  push_cast
  rw [hnorm']
  simp only [hcast]
  have hterm : ∀ q : Fin d × Fin d,
      ((swapTestState (WithLp.ofLp ψ) (WithLp.ofLp ϕ) (0, q) : ℂ) *
        conj (swapTestState (WithLp.ofLp ψ) (WithLp.ofLp ϕ) (0, q)))
        = (4 : ℂ)⁻¹ * ((ψ q.1 * ϕ q.2 + ψ q.2 * ϕ q.1) *
            (conj (ψ q.1) * conj (ϕ q.2) + conj (ψ q.2) * conj (ϕ q.1))) := by
    rintro ⟨i, j⟩
    rw [swapTestState_zero]
    simp only [map_mul, map_add, map_inv₀, Complex.conj_ofNat]
    ring
  rw [Finset.sum_congr rfl fun q _ => hterm q, ← Finset.mul_sum, Fintype.sum_prod_type,
    sum_expand, hψ1, hϕ1, hAc]
  ring

/-- Expansion of the double sum occurring in the rejection probability. -/
private theorem sum_expand_sub (ψ ϕ : Fin d → ℂ) :
    ∑ i, ∑ j, (ψ i * ϕ j - ψ j * ϕ i) *
        (conj (ψ i) * conj (ϕ j) - conj (ψ j) * conj (ϕ i))
      = 2 * ((∑ i, ψ i * conj (ψ i)) * (∑ j, ϕ j * conj (ϕ j)))
        - 2 * ((∑ i, ψ i * conj (ϕ i)) * (∑ j, ϕ j * conj (ψ j))) := by
  have h1 : ∀ f g : Fin d → ℂ, ∑ i, ∑ j, f i * g j = (∑ i, f i) * (∑ j, g j) := by
    intro f g; rw [Finset.sum_mul_sum]
  have h2 : ∀ f g : Fin d → ℂ, ∑ i, ∑ j, f j * g i = (∑ j, f j) * (∑ i, g i) := by
    intro f g; rw [Finset.sum_comm, Finset.sum_mul_sum]
  have e : ∀ i j : Fin d,
      (ψ i * ϕ j - ψ j * ϕ i) * (conj (ψ i) * conj (ϕ j) - conj (ψ j) * conj (ϕ i))
        = (ψ i * conj (ψ i)) * (ϕ j * conj (ϕ j)) - (ψ i * conj (ϕ i)) * (ϕ j * conj (ψ j))
          + (ψ j * conj (ψ j)) * (ϕ i * conj (ϕ i))
          - (ψ j * conj (ϕ j)) * (ϕ i * conj (ψ i)) := by
    intro i j; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2]
  ring

/-- The SWAP test *rejects* when the final measurement of the ancilla yields
`1`; this is the probability of that outcome. -/
noncomputable def swapTestRejectProb (ψ ϕ : Fin d → ℂ) : ℝ :=
  ∑ q : Fin d × Fin d, ‖swapTestState ψ ϕ (1, q)‖ ^ 2

/-- For unit vectors `ψ` and `ϕ`, the SWAP test rejects (measures `1` on the
ancilla) with probability `(1 - |⟨ψ|ϕ⟩|²)/2`. -/
theorem swap_test_reject (ψ ϕ : EuclideanSpace ℂ (Fin d))
    (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    swapTestRejectProb (WithLp.ofLp ψ) (WithLp.ofLp ϕ)
      = (1 - ‖(inner ℂ ψ ϕ : ℂ)‖ ^ 2) / 2 := by
  have hinner : (inner ℂ ψ ϕ : ℂ) = ∑ i, conj (ψ i) * ϕ i := by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hψ1 : ∑ i, ψ i * conj (ψ i) = (1 : ℂ) := sum_mul_conj_self_of_norm_one ψ hψ
  have hϕ1 : ∑ i, ϕ i * conj (ϕ i) = (1 : ℂ) := sum_mul_conj_self_of_norm_one ϕ hϕ
  set A : ℂ := ∑ i, ψ i * conj (ϕ i) with hA
  have hAc : ∑ i, ϕ i * conj (ψ i) = conj A := by
    rw [hA, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, Complex.conj_conj, mul_comm]
  have hnorm : ((‖(inner ℂ ψ ϕ : ℂ)‖ ^ 2 : ℝ) : ℂ) = A * conj A := by
    rw [ofReal_norm_sq, hinner]
    have h : ∑ i, conj (ψ i) * ϕ i = conj A := by
      rw [hA, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, Complex.conj_conj, mul_comm]
    rw [h, Complex.conj_conj]
    ring
  have hcast : ∀ z : ℂ, ((‖z‖ : ℂ)) ^ 2 = z * conj z := by
    intro z
    rw [← Complex.ofReal_pow]
    exact ofReal_norm_sq z
  have hnorm' : ((‖(inner ℂ ψ ϕ : ℂ)‖ : ℂ)) ^ 2 = A * conj A := by
    rw [← Complex.ofReal_pow]; exact hnorm
  refine Complex.ofReal_inj.mp ?_
  rw [swapTestRejectProb]
  push_cast
  rw [hnorm']
  simp only [hcast]
  have hterm : ∀ q : Fin d × Fin d,
      ((swapTestState (WithLp.ofLp ψ) (WithLp.ofLp ϕ) (1, q) : ℂ) *
        conj (swapTestState (WithLp.ofLp ψ) (WithLp.ofLp ϕ) (1, q)))
        = (4 : ℂ)⁻¹ * ((ψ q.1 * ϕ q.2 - ψ q.2 * ϕ q.1) *
            (conj (ψ q.1) * conj (ϕ q.2) - conj (ψ q.2) * conj (ϕ q.1))) := by
    rintro ⟨i, j⟩
    rw [swapTestState_one]
    simp only [map_mul, map_sub, map_inv₀, Complex.conj_ofNat]
    ring
  rw [Finset.sum_congr rfl fun q _ => hterm q, ← Finset.mul_sum, Fintype.sum_prod_type,
    sum_expand_sub, hψ1, hϕ1, hAc]
  ring

/-- Sanity check: the two measurement outcomes of the SWAP test have
probabilities summing to `1`. -/
theorem swap_test_probs_sum_one (ψ ϕ : EuclideanSpace ℂ (Fin d))
    (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    swapTestAcceptProb (WithLp.ofLp ψ) (WithLp.ofLp ϕ)
      + swapTestRejectProb (WithLp.ofLp ψ) (WithLp.ofLp ϕ) = 1 := by
  rw [swap_test_overlap ψ ϕ hψ hϕ, swap_test_reject ψ ϕ hψ hϕ]
  ring

end QC

