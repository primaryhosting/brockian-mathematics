import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The commutator `[A, B] = AB - BA` of two linear operators on `E`. -/
def comm (A B : Module.End ℂ E) : Module.End ℂ E := A * B - B * A

@[simp] lemma comm_apply (A B : Module.End ℂ E) (v : E) :
    comm A B v = A (B v) - B (A v) := rfl

/-- Leibniz rule: `[A, BC] = B [A, C] + [A, B] C`. -/
lemma comm_mul_right (A B C : Module.End ℂ E) :
    comm A (B * C) = B * comm A C + comm A B * C := by
  simp only [comm]; noncomm_ring

/-- If `[A, B]` is a scalar `c`, then `[A², B] = 2c • A`. -/
lemma comm_sq_left {A B : Module.End ℂ E} {c : ℂ} (h : comm A B = c • 1) :
    comm (A * A) B = (2 * c) • A := by
  have e : comm (A * A) B = A * comm A B + comm A B * A := by simp only [comm]; noncomm_ring
  rw [e, h]
  simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, two_mul, add_smul]

lemma comm_smul_left (c : ℂ) (A B : Module.End ℂ E) : comm (c • A) B = c • comm A B := by
  simp only [comm, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]

lemma comm_add_left (A B C : Module.End ℂ E) : comm (A + B) C = comm A C + comm B C := by
  simp only [comm]; noncomm_ring

lemma comm_sum_right {ι : Type*} (s : Finset ι) (A : Module.End ℂ E) (g : ι → Module.End ℂ E) :
    comm A (∑ k ∈ s, g k) = ∑ k ∈ s, comm A (g k) := by
  simp only [comm, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

lemma comm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Module.End ℂ E) (B : Module.End ℂ E) :
    comm (∑ j ∈ s, f j) B = ∑ j ∈ s, comm (f j) B := by
  simp only [comm, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

/-- Commutator of the (unnormalised) kinetic term with the virial generator
`G = Σ xₖ pₖ`: it equals `-2iħ Σ pⱼ²`. -/
lemma comm_kinetic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x p : ι → Module.End ℂ E) (hbar : ℝ)
    (ccr : ∀ j k, comm (x j) (p k) = (if j = k then (hbar * Complex.I) else 0) • 1)
    (hpp : ∀ j k, p j * p k = p k * p j) :
    comm (∑ j, p j * p j) (∑ k, x k * p k)
      = (-(2 * (hbar * Complex.I))) • ∑ j, p j * p j := by
  rw [comm_sum_left, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [comm_sum_right]
  have key : ∀ k : ι, comm (p j * p j) (x k * p k)
      = (if j = k then (-(2 * (hbar * Complex.I))) • (p j * p j) else 0) := by
    intro k
    rw [comm_mul_right]
    have h1 : comm (p j * p j) (p k) = 0 := by
      simp only [comm]
      rw [mul_assoc, hpp j k, ← mul_assoc, hpp j k, mul_assoc, sub_self]
    have h2 : comm (p j) (x k) = (if j = k then (-(hbar * Complex.I)) else 0) • 1 := by
      have e : comm (p j) (x k) = - comm (x k) (p j) := by simp only [comm]; noncomm_ring
      rw [e, ccr k j]
      by_cases h : j = k <;> simp [h, eq_comm, ← neg_smul]
    rw [comm_sq_left h2, h1]
    by_cases h : j = k <;> simp [h, mul_comm, Algebra.smul_mul_assoc]
  rw [Finset.sum_congr rfl (fun k _ => key k)]
  simp

/-- Commutator of the potential with the virial generator `G = Σ xₖ pₖ`:
it equals `iħ Σ xₖ Wₖ`, i.e. `iħ (r · ∇V)`. -/
lemma comm_potential {ι : Type*} [Fintype ι]
    (x W p : ι → Module.End ℂ E) (V : Module.End ℂ E) (hbar : ℝ)
    (hVx : ∀ j, V * x j = x j * V)
    (hVp : ∀ j, comm V (p j) = (hbar * Complex.I) • W j) :
    comm V (∑ k, x k * p k) = (hbar * Complex.I) • ∑ k, x k * W k := by
  rw [comm_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [comm_mul_right, hVp k]
  have h0 : comm V (x k) = 0 := by simp only [comm, hVx k, sub_self]
  rw [h0]
  simp [Algebra.mul_smul_comm]

/-- Expectation value of a commutator with the Hamiltonian vanishes in a stationary state. -/
lemma inner_comm_eq_zero (H G : Module.End ℂ E)
    (hHsymm : ∀ u v : E, ⟪H u, v⟫_ℂ = ⟪u, H v⟫_ℂ)
    (psi : E) (En : ℝ) (heig : H psi = (En : ℂ) • psi) :
    ⟪psi, comm H G psi⟫_ℂ = 0 := by
  have h1 : comm H G psi = H (G psi) - G (H psi) := rfl
  rw [h1, inner_sub_right, ← hHsymm, heig, inner_smul_left, map_smul, inner_smul_right]
  simp [Complex.conj_ofReal]

/-- **Quantum virial theorem.**

Let `x j`, `p j` (with `j` ranging over a finite set of spatial directions) be position and
momentum operators on a complex inner product space `E`, satisfying the canonical
commutation relations `[xⱼ, p_k] = i ħ δⱼk`, the momenta commuting among themselves.
Let `V` be a potential commuting with the positions, and let `W j` be its directional
derivative operators, characterised by `[V, pⱼ] = i ħ Wⱼ` (so `Wⱼ = ∂ⱼ V`).

Let `T = (1/2m) Σⱼ pⱼ²` be the kinetic energy and `H = T + V` the Hamiltonian, assumed
symmetric.  If `psi` is a normalised bound stationary state, i.e. an eigenvector of `H`
with real energy `En`, then

`2 ⟨T⟩ = ⟨r · ∇V⟩`,  i.e.  `2 ⟪psi, T psi⟫ = ⟪psi, (Σⱼ xⱼ Wⱼ) psi⟫`.

(The normalisation hypothesis `‖psi‖ = 1` is part of the physical statement and is kept,
although the proof does not need it: the identity between the two unnormalised quadratic
forms holds for every stationary state.) -/
theorem virial_theorem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x p W : ι → Module.End ℂ E) (V T H : Module.End ℂ E) (hbar m : ℝ)
    (hhbar : hbar ≠ 0)
    (ccr : ∀ j k, comm (x j) (p k) = (if j = k then (hbar * Complex.I) else 0) • 1)
    (hpp : ∀ j k, p j * p k = p k * p j)
    (hVx : ∀ j, V * x j = x j * V)
    (hVp : ∀ j, comm V (p j) = (hbar * Complex.I) • W j)
    (hT : T = (((1 : ℂ) / (2 * m)) • ∑ j, p j * p j))
    (hH : H = T + V)
    (hHsymm : ∀ u v : E, ⟪H u, v⟫_ℂ = ⟪u, H v⟫_ℂ)
    (psi : E) (hnorm : ‖psi‖ = 1) (En : ℝ) (heig : H psi = (En : ℂ) • psi) :
    2 * ⟪psi, T psi⟫_ℂ = ⟪psi, (∑ j, x j * W j) psi⟫_ℂ := by
  set G : Module.End ℂ E := ∑ k, x k * p k with hG
  -- the algebraic identity `[H, G] = -iħ (2T - Σ xⱼ Wⱼ)`
  have hcomm : comm H G
      = (-(hbar * Complex.I)) • ((2 : ℂ) • T - ∑ j, x j * W j) := by
    rw [hH, comm_add_left, hT, comm_smul_left, hG, comm_kinetic x p hbar ccr hpp,
      comm_potential x W p V hbar hVx hVp]
    module
  -- the expectation value of `[H, G]` vanishes in the stationary state
  have hzero : ⟪psi, comm H G psi⟫_ℂ = 0 := inner_comm_eq_zero H G hHsymm psi En heig
  rw [hcomm] at hzero
  have happ : ((-(hbar * Complex.I)) • ((2 : ℂ) • T - ∑ j, x j * W j)) psi
      = (-(hbar * Complex.I)) • ((2 : ℂ) • T psi - (∑ j, x j * W j) psi) := by
    simp [LinearMap.smul_apply, smul_sub]
  rw [happ, inner_smul_right, inner_sub_right, inner_smul_right] at hzero
  have hne : (-((hbar : ℂ) * Complex.I)) ≠ 0 := by
    simp [Complex.ext_iff, hhbar]
  have := mul_eq_zero.mp hzero
  rcases this with h | h
  · exact absurd h hne
  · linear_combination h

end Phys

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

