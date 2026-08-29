/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QPhys

noncomputable section

/-- The (algebraic) Fock space of the one–dimensional quantum harmonic oscillator:
finitely supported complex combinations of the number states `|n⟩`, `n : ℕ`. -/
abbrev Fock := ℕ →₀ ℂ

/-- The number state `|n⟩`. -/
def ket (n : ℕ) : Fock := Finsupp.single n (1 : ℂ)

/-- The annihilation (lowering) ladder operator: `a |n⟩ = √n |n-1⟩`. -/
def aOp : Fock →ₗ[ℂ] Fock :=
  Finsupp.lsum ℂ fun n =>
    LinearMap.toSpanSingleton ℂ Fock (Finsupp.single (n - 1) ((Real.sqrt n : ℝ) : ℂ))

/-- The creation (raising) ladder operator: `a† |n⟩ = √(n+1) |n+1⟩`. -/
def aDagOp : Fock →ₗ[ℂ] Fock :=
  Finsupp.lsum ℂ fun n =>
    LinearMap.toSpanSingleton ℂ Fock (Finsupp.single (n + 1) ((Real.sqrt (n + 1) : ℝ) : ℂ))

/-- The number operator `N = a† a`. -/
def numberOp : Fock →ₗ[ℂ] Fock := aDagOp ∘ₗ aOp

/-- The Hamiltonian of the harmonic oscillator, `H = ℏω (a†a + 1/2)`. -/
def hamiltonian (hbar omega : ℝ) : Fock →ₗ[ℂ] Fock :=
  ((hbar * omega : ℝ) : ℂ) • (numberOp + ((1 / 2 : ℂ)) • LinearMap.id)

/-- The `n`-th energy level `ℏω (n + 1/2)`. -/
def energy (hbar omega : ℝ) (n : ℕ) : ℝ := hbar * omega * (n + 1 / 2)

private lemma sqrt_mul_self_cast (n : ℕ) :
    ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  simp

lemma aOp_single (n : ℕ) (c : ℂ) :
    aOp (Finsupp.single n c) = Finsupp.single (n - 1) (((Real.sqrt n : ℝ) : ℂ) * c) := by
  simp [aOp, LinearMap.toSpanSingleton, Finsupp.smul_single, mul_comm]

lemma aDagOp_single (n : ℕ) (c : ℂ) :
    aDagOp (Finsupp.single n c)
      = Finsupp.single (n + 1) (((Real.sqrt (n + 1) : ℝ) : ℂ) * c) := by
  simp [aDagOp, LinearMap.toSpanSingleton, Finsupp.smul_single, mul_comm]

lemma aOp_ket_zero : aOp (ket 0) = 0 := by
  simp [ket, aOp_single]

lemma aOp_ket_succ (n : ℕ) :
    aOp (ket (n + 1)) = ((Real.sqrt (n + 1) : ℝ) : ℂ) • ket n := by
  simp [ket, aOp_single, Finsupp.smul_single]

lemma aDagOp_ket (n : ℕ) :
    aDagOp (ket n) = ((Real.sqrt (n + 1) : ℝ) : ℂ) • ket (n + 1) := by
  simp [ket, aDagOp_single, Finsupp.smul_single]

/-- The canonical commutation relation `[a, a†] = 1`. -/
theorem ladder_ccr : aOp ∘ₗ aDagOp - aDagOp ∘ₗ aOp = LinearMap.id := by
  refine Finsupp.lhom_ext' fun n => LinearMap.ext fun c => ?_
  cases n with
  | zero =>
      simp [aOp_single, aDagOp_single]
  | succ m =>
      have h1 : ((Real.sqrt (m + 1 + 1) : ℝ) : ℂ) * (((Real.sqrt (m + 1 + 1) : ℝ) : ℂ) * c)
          = ((m : ℂ) + 2) * c := by
        rw [← mul_assoc]
        have := sqrt_mul_self_cast (m + 2)
        push_cast at this ⊢
        rw [show ((m : ℝ) + 1 + 1) = ((m : ℝ) + 2) by ring, this]
      have h2 : ((Real.sqrt (m + 1) : ℝ) : ℂ) * (((Real.sqrt (m + 1) : ℝ) : ℂ) * c)
          = ((m : ℂ) + 1) * c := by
        rw [← mul_assoc]
        have := sqrt_mul_self_cast (m + 1)
        push_cast at this ⊢
        rw [this]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
        Finsupp.lsingle_apply, aOp_single, aDagOp_single, Nat.succ_sub_one]
      push_cast
      rw [h1, h2, ← Finsupp.single_sub]
      ring_nf

lemma numberOp_single (n : ℕ) (c : ℂ) :
    numberOp (Finsupp.single n c) = Finsupp.single n ((n : ℂ) * c) := by
  cases n with
  | zero => simp [numberOp, aOp_single]
  | succ m =>
      simp only [numberOp, LinearMap.comp_apply, aOp_single, aDagOp_single,
        Nat.succ_sub_one]
      congr 1
      rw [← mul_assoc]
      have := sqrt_mul_self_cast (m + 1)
      push_cast at this ⊢
      rw [this]

/-- The number operator is diagonal in the number basis. -/
lemma numberOp_apply (f : Fock) (k : ℕ) : numberOp f k = (k : ℂ) * f k := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, mul_add]
  | single a b =>
      rw [numberOp_single, Finsupp.single_apply, Finsupp.single_apply]
      by_cases h : a = k <;> simp [h]

/-- `N |n⟩ = n |n⟩`. -/
lemma numberOp_ket (n : ℕ) : numberOp (ket n) = (n : ℂ) • ket n := by
  simp [ket, numberOp_single, Finsupp.smul_single]

/-- The Hamiltonian is diagonal in the number basis, with entries the energies. -/
lemma hamiltonian_apply (hbar omega : ℝ) (f : Fock) (k : ℕ) :
    hamiltonian hbar omega f k = ((energy hbar omega k : ℝ) : ℂ) * f k := by
  simp only [hamiltonian, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    Finsupp.coe_smul, Finsupp.add_apply, Pi.smul_apply, smul_eq_mul, numberOp_apply, energy]
  push_cast
  ring

/-- Each number state is an eigenvector of `H` with eigenvalue `ℏω (n + 1/2)`. -/
theorem hamiltonian_ket (hbar omega : ℝ) (n : ℕ) :
    hamiltonian hbar omega (ket n) = ((energy hbar omega n : ℝ) : ℂ) • ket n := by
  ext k
  rw [hamiltonian_apply]
  simp only [ket, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply]
  by_cases h : n = k <;> simp [h]

lemma ket_ne_zero (n : ℕ) : ket n ≠ 0 := by
  simp [ket, Finsupp.single_eq_zero]

/-- `[N, a] = -a`: the annihilation operator lowers the number eigenvalue by one. -/
theorem numberOp_comm_aOp : numberOp ∘ₗ aOp - aOp ∘ₗ numberOp = -aOp := by
  refine Finsupp.lhom_ext' fun n => LinearMap.ext fun c => ?_
  cases n with
  | zero => simp [aOp_single, numberOp_single]
  | succ m =>
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply,
        Finsupp.lsingle_apply, aOp_single, numberOp_single, Nat.succ_sub_one]
      rw [← Finsupp.single_sub, ← Finsupp.single_neg]
      congr 1
      push_cast
      ring

/-- `[N, a†] = a†`: the creation operator raises the number eigenvalue by one. -/
theorem numberOp_comm_aDagOp : numberOp ∘ₗ aDagOp - aDagOp ∘ₗ numberOp = aDagOp := by
  refine Finsupp.lhom_ext' fun n => LinearMap.ext fun c => ?_
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
    aDagOp_single, numberOp_single]
  rw [← Finsupp.single_sub]
  congr 1
  push_cast
  ring

/--
**Spectrum of the quantum harmonic oscillator.**

For the Hamiltonian `H = ℏω (a†a + 1/2)` built from the ladder operators `a`, `a†`
(which satisfy `[a, a†] = 1`, see `QPhys.ladder_ccr`) acting on the Fock space,
the set of eigenvalues of `H` is exactly `{ℏω (n + 1/2) : n ∈ ℕ}`.
-/
theorem oscillator_spectrum (hbar omega : ℝ) :
    {E : ℂ | ∃ v : Fock, v ≠ 0 ∧ hamiltonian hbar omega v = E • v}
      = {E : ℂ | ∃ n : ℕ, E = ((energy hbar omega n : ℝ) : ℂ)} := by
  ext E
  constructor
  · rintro ⟨v, hv, hEv⟩
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (Finsupp.ext h)
    refine ⟨k, ?_⟩
    have := congrArg (fun w : Fock => w k) hEv
    simp only [hamiltonian_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_right_cancel₀ hk this).symm
  · rintro ⟨n, rfl⟩
    exact ⟨ket n, ket_ne_zero n, hamiltonian_ket hbar omega n⟩

end

end QPhys

