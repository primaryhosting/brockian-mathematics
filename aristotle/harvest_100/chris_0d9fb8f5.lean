/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede every command, including module docstrings,
-- so the header above is a plain comment and is repeated as a module docstring below.)
import Mathlib

/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Finsupp

/-- The `n`-th number state `|n⟩`, realised as a basis vector of the space of
finitely supported functions `ℕ →₀ ℂ` (the algebraic Fock space). -/
noncomputable def ket (n : ℕ) : ℕ →₀ ℂ := Finsupp.single n 1

lemma ket_ne_zero (n : ℕ) : ket n ≠ 0 := by
  simp [ket, Finsupp.single_eq_zero]

/-- The annihilation (lowering) ladder operator `a`, determined by `a |n⟩ = √n |n-1⟩`. -/
noncomputable def annih : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n => LinearMap.id.smulRight ((Real.sqrt n : ℂ) • ket (n - 1))

/-- The creation (raising) ladder operator `a†`, determined by `a† |n⟩ = √(n+1) |n+1⟩`. -/
noncomputable def create : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n => LinearMap.id.smulRight ((Real.sqrt (n + 1) : ℂ) • ket (n + 1))

/-- The number operator `N = a† a`. -/
noncomputable def number : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) := create.comp annih

/-- The Hamiltonian `H = ℏω (N + 1/2)` of the quantum harmonic oscillator. -/
noncomputable def hamiltonian (hbar omega : ℝ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  ((hbar * omega : ℝ) : ℂ) • (number + (1 / 2 : ℂ) • LinearMap.id)

lemma annih_single (n : ℕ) (c : ℂ) :
    annih (Finsupp.single n c) = (c * (Real.sqrt n : ℂ)) • ket (n - 1) := by
  simp [annih, Finsupp.lsum_single, smul_smul, mul_comm]

lemma create_single (n : ℕ) (c : ℂ) :
    create (Finsupp.single n c) = (c * (Real.sqrt (n + 1) : ℂ)) • ket (n + 1) := by
  simp [create, Finsupp.lsum_single, smul_smul, mul_comm]

lemma annih_ket (n : ℕ) : annih (ket n) = (Real.sqrt n : ℂ) • ket (n - 1) := by
  simp [ket, annih_single]

lemma create_ket (n : ℕ) : create (ket n) = (Real.sqrt (n + 1) : ℂ) • ket (n + 1) := by
  simp [ket, create_single]

private lemma sqrt_sq_cast (n : ℕ) :
    ((Real.sqrt n : ℂ)) * ((Real.sqrt n : ℂ)) = (n : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  simp

/-- The number states are eigenvectors of `N` with eigenvalue `n`. -/
lemma number_ket (n : ℕ) : number (ket n) = (n : ℂ) • ket n := by
  cases n with
  | zero => simp [number, annih_ket, ket]
  | succ m =>
      have h : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
      simp only [number, LinearMap.comp_apply, annih_ket, map_smul, create_ket]
      rw [smul_smul]
      simp only [Nat.add_sub_cancel]
      congr 1
      · rw [← h] at *
        push_cast
        rw [sqrt_sq_cast]
        push_cast
        ring
      · simp

/-- The canonical commutation relation `[a, a†] = 1` for the ladder operators. -/
theorem ladder_commutator :
    annih.comp create - create.comp annih = (LinearMap.id : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ)) := by
  apply Finsupp.lhom_ext
  intro n c
  have h : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, create_single,
    annih_single, map_smul, annih_ket, create_ket, Nat.add_sub_cancel]
  rw [smul_smul, smul_smul]
  have hs : ((Real.sqrt ((n : ℝ) + 1) : ℂ)) * ((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ)) = ((n : ℂ) + 1) := by
    rw [← h, sqrt_sq_cast (n + 1)]
    push_cast; ring
  have hs' : ((Real.sqrt ((n : ℝ)) : ℂ)) * ((Real.sqrt (((n - 1 : ℕ) : ℝ) + 1) : ℂ)) = (n : ℂ) := by
    cases n with
    | zero => simp
    | succ m =>
        have : (((m + 1 - 1 : ℕ) : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by
          simp; push_cast; ring
        rw [this, sqrt_sq_cast (m + 1)]
  rw [show (c * (Real.sqrt ((n : ℝ) + 1) : ℂ)) * (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ)
        = c * (((Real.sqrt ((n : ℝ) + 1) : ℂ)) * ((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))) by ring,
      hs,
      show (c * (Real.sqrt ((n : ℝ)) : ℂ)) * (Real.sqrt (((n - 1 : ℕ) : ℝ) + 1) : ℂ)
        = c * (((Real.sqrt ((n : ℝ)) : ℂ)) * ((Real.sqrt (((n - 1 : ℕ) : ℝ) + 1) : ℂ))) by ring,
      hs']
  cases n with
  | zero => simp [ket]
  | succ m =>
      simp only [Nat.add_sub_cancel, ket]
      rw [← sub_smul]
      push_cast
      rw [show ((m : ℂ) + 1 + 1) - ((m : ℂ) + 1) = 1 by ring, one_smul]

/-- `N` acts diagonally: the `k`-th coefficient of `N v` is `k` times that of `v`. -/
lemma number_apply (v : ℕ →₀ ℂ) (k : ℕ) : (number v) k = (k : ℂ) * v k := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]; ring
  | single n c =>
      have : Finsupp.single n c = c • ket n := by simp [ket, Finsupp.smul_single]
      rw [this, map_smul, number_ket]
      by_cases h : k = n <;> simp [ket, h, Finsupp.single_apply, mul_comm, mul_left_comm]

lemma hamiltonian_apply (hbar omega : ℝ) (v : ℕ →₀ ℂ) (k : ℕ) :
    (hamiltonian hbar omega v) k = (((hbar * omega : ℝ) : ℂ) * ((k : ℂ) + 1 / 2)) * v k := by
  simp [hamiltonian, number_apply]
  ring

/-- The number states are eigenvectors of the oscillator Hamiltonian with
energies `ℏω(n + 1/2)`. -/
theorem hamiltonian_ket (hbar omega : ℝ) (n : ℕ) :
    hamiltonian hbar omega (ket n) = (((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2)) • ket n := by
  simp only [hamiltonian, number_ket, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, smul_add, smul_smul]
  rw [← add_smul]
  congr 1
  ring

/-- **Spectrum of the quantum harmonic oscillator.**

For the Hamiltonian `H = ℏω (a†a + 1/2)` built from the ladder operators `a`, `a†`
on the (algebraic) Fock space `ℕ →₀ ℂ`, the set of eigenvalues of `H` is exactly
`{ℏω (n + 1/2) : n ∈ ℕ}`. -/
theorem oscillator_spectrum (hbar omega : ℝ) (hhbar : 0 < hbar) (homega : 0 < omega) :
    {lam : ℂ | ∃ v : ℕ →₀ ℂ, v ≠ 0 ∧ hamiltonian hbar omega v = lam • v}
      = {lam : ℂ | ∃ n : ℕ, lam = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2)} := by
  ext lam
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, hEq⟩
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (Finsupp.ext h)
    refine ⟨k, ?_⟩
    have := congrArg (fun w => w k) hEq
    simp only [hamiltonian_apply, Finsupp.smul_apply, smul_eq_mul] at this
    field_simp at this
    rcases mul_eq_mul_right_iff.mp this with h | h
    · exact h
    · exact absurd h hk
  · rintro ⟨n, rfl⟩
    exact ⟨ket n, ket_ne_zero n, hamiltonian_ket hbar omega n⟩

end QPhys

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

