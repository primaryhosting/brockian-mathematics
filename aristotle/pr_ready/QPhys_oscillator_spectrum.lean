/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Statement: The quantum harmonic oscillator has spectrum {ℏω(n+½) : n∈ℕ} via ladder operators.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QPhys

/-- The state space of the quantum harmonic oscillator, in the occupation-number
(Fock) representation: a state is described by its sequence of coefficients in the
number basis. -/
abbrev Fock : Type := ℕ → ℂ

/-- The `n`-th number-basis state `|n⟩`. -/
noncomputable def basisState (n : ℕ) : Fock := fun m => if m = n then 1 else 0

/-- The annihilation (lowering) operator `a`, with `a |n⟩ = √n |n-1⟩`. -/
noncomputable def annihilation : Fock →ₗ[ℂ] Fock where
  toFun v := fun n => (Real.sqrt (n + 1) : ℂ) * v (n + 1)
  map_add' u v := by funext n; simp [mul_add]
  map_smul' c v := by funext n; simp [smul_eq_mul]; ring

/-- The creation (raising) operator `a†`, with `a† |n⟩ = √(n+1) |n+1⟩`. -/
noncomputable def creation : Fock →ₗ[ℂ] Fock where
  toFun v := fun n => (Real.sqrt n : ℂ) * v (n - 1)
  map_add' u v := by funext n; simp [mul_add]
  map_smul' c v := by funext n; simp [smul_eq_mul]; ring

/-- The number operator `N = a† a`. -/
noncomputable def numberOp : Fock →ₗ[ℂ] Fock := creation ∘ₗ annihilation

/-- The Hamiltonian of the quantum harmonic oscillator,
`H = ℏω (a† a + 1/2)`. -/
noncomputable def hamiltonian (hbar omega : ℝ) : Fock →ₗ[ℂ] Fock :=
  ((hbar * omega : ℝ) : ℂ) • (numberOp + ((1 / 2 : ℂ) • LinearMap.id))

section Basic

lemma annihilation_apply (v : Fock) (n : ℕ) :
    annihilation v n = (Real.sqrt (n + 1) : ℂ) * v (n + 1) := rfl

lemma creation_apply (v : Fock) (n : ℕ) :
    creation v n = (Real.sqrt n : ℂ) * v (n - 1) := rfl

lemma sqrt_mul_self_cast (x : ℝ) (hx : 0 ≤ x) :
    ((Real.sqrt x : ℂ)) * (Real.sqrt x : ℂ) = (x : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]

/-- The number operator is diagonal in the number basis: `(N v) n = n * v n`. -/
lemma numberOp_apply (v : Fock) (n : ℕ) : numberOp v n = (n : ℂ) * v n := by
  cases n with
  | zero => simp [numberOp, creation_apply]
  | succ m =>
      simp only [numberOp, LinearMap.comp_apply, creation_apply, annihilation_apply,
        Nat.succ_sub_one]
      push_cast
      rw [← mul_assoc, sqrt_mul_self_cast _ (by positivity)]
      push_cast
      ring

/-- The canonical commutation relation `[a, a†] = 1`. -/
lemma commutator_annihilation_creation :
    annihilation ∘ₗ creation - creation ∘ₗ annihilation = LinearMap.id := by
  ext v n
  have hac : annihilation (creation v) n = ((n : ℂ) + 1) * v n := by
    rw [annihilation_apply, creation_apply]
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [← mul_assoc, sqrt_mul_self_cast _ (by positivity)]
    push_cast
    ring
  have hca : creation (annihilation v) n = (n : ℂ) * v n := numberOp_apply v n
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, Pi.sub_apply]
  rw [hac, hca]
  ring

/-- Action of the lowering operator on a number state: `a |n+1⟩ = √(n+1) |n⟩`. -/
lemma annihilation_basisState (n : ℕ) :
    annihilation (basisState (n + 1)) = (Real.sqrt (n + 1) : ℂ) • basisState n := by
  funext m
  by_cases h : m = n
  · subst h; simp [annihilation_apply, basisState]
  · simp [annihilation_apply, basisState, h]

lemma annihilation_basisState_zero : annihilation (basisState 0) = 0 := by
  funext m
  simp [annihilation_apply, basisState]

/-- Action of the raising operator on a number state: `a† |n⟩ = √(n+1) |n+1⟩`. -/
lemma creation_basisState (n : ℕ) :
    creation (basisState n) = (Real.sqrt (n + 1) : ℂ) • basisState (n + 1) := by
  funext m
  cases m with
  | zero => simp [creation_apply, basisState]
  | succ k =>
      by_cases h : k = n
      · subst h; simp [creation_apply, basisState]
      · simp [creation_apply, basisState, h]

lemma basisState_ne_zero (n : ℕ) : basisState n ≠ 0 := by
  intro h
  have : basisState n n = 0 := by rw [h]; rfl
  simp [basisState] at this

lemma hamiltonian_apply (hbar omega : ℝ) (v : Fock) (n : ℕ) :
    hamiltonian hbar omega v n = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2) * v n := by
  simp only [hamiltonian, LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply,
    LinearMap.id_apply, smul_eq_mul, Pi.add_apply]
  rw [numberOp_apply]
  ring

/-- Each number state `|n⟩` is an eigenstate of `H` with eigenvalue `ℏω(n + 1/2)`. -/
lemma hamiltonian_basisState (hbar omega : ℝ) (n : ℕ) :
    hamiltonian hbar omega (basisState n)
      = (((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2)) • basisState n := by
  funext m
  rw [hamiltonian_apply]
  by_cases h : m = n
  · subst h; simp [basisState]
  · simp [basisState, h]

end Basic

/-- **Spectrum of the quantum harmonic oscillator.**
For the Hamiltonian `H = ℏω (a†a + 1/2)` built from the ladder operators `a`, `a†`
acting on the Fock space of occupation-number sequences, the set of eigenvalues of
`H` is exactly `{ℏω(n + 1/2) : n ∈ ℕ}`. -/
theorem oscillator_spectrum (hbar omega : ℝ) :
    {lam : ℂ | ∃ v : Fock, v ≠ 0 ∧ hamiltonian hbar omega v = lam • v}
      = {lam : ℂ | ∃ n : ℕ, lam = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2)} := by
  ext lam
  constructor
  · rintro ⟨v, hv, hHv⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, v n ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (funext fun n => h n)
    refine ⟨n, ?_⟩
    have h1 : hamiltonian hbar omega v n = lam * v n := by
      rw [hHv]; rfl
    rw [hamiltonian_apply] at h1
    exact (mul_right_cancel₀ hn h1).symm
  · rintro ⟨n, rfl⟩
    exact ⟨basisState n, basisState_ne_zero n, hamiltonian_basisState hbar omega n⟩

end QPhys

