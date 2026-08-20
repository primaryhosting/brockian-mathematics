/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-! ## The Fock space of the harmonic oscillator

We model the oscillator on the Fock (occupation-number) space: a state is a family of
complex amplitudes indexed by the occupation number `n : ℕ`, i.e. an element of `ℕ → ℂ`.
The `n`-th basis state `fockBasis n` is the state with a single unit amplitude at level `n`.
-/

/-- States of the harmonic oscillator, described by their amplitudes in the number basis. -/
abbrev Fock := ℕ → ℂ

/-- The `n`-th number eigenstate `|n⟩`. -/
noncomputable def fockBasis (n : ℕ) : Fock := fun m => if m = n then (1 : ℂ) else 0

/-- The annihilation (lowering) operator `a`, determined by `a |n+1⟩ = √(n+1) |n⟩`,
    `a |0⟩ = 0`. -/
noncomputable def annih : Fock →ₗ[ℂ] Fock where
  toFun v := fun n => (Real.sqrt (n + 1) : ℂ) * v (n + 1)
  map_add' u v := by funext n; simp [mul_add]
  map_smul' c v := by funext n; simp [mul_left_comm]

/-- The creation (raising) operator `a†`, determined by `a† |n⟩ = √(n+1) |n+1⟩`. -/
noncomputable def creat : Fock →ₗ[ℂ] Fock where
  toFun v := fun n => (Real.sqrt n : ℂ) * v (n - 1)
  map_add' u v := by funext n; simp [mul_add]
  map_smul' c v := by funext n; simp [mul_left_comm]

/-- The number operator `N = a† a`. -/
noncomputable def number : Fock →ₗ[ℂ] Fock := creat ∘ₗ annih

/-- The Hamiltonian `H = ℏω (a† a + 1/2)` of the quantum harmonic oscillator. -/
noncomputable def hamiltonian (hbar omega : ℝ) : Fock →ₗ[ℂ] Fock :=
  ((hbar * omega : ℝ) : ℂ) • (number + (1 / 2 : ℂ) • LinearMap.id)

/-! ## Basic computations -/

private lemma sqrt_succ_sq (n : ℕ) :
    ((Real.sqrt ((n : ℝ) + 1) : ℂ)) * ((Real.sqrt ((n : ℝ) + 1) : ℂ)) = (n : ℂ) + 1 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast; ring

/-- The canonical commutation relation `[a, a†] = 1`. -/
theorem commutator_annih_creat (v : Fock) : annih (creat v) - creat (annih v) = v := by
  funext n
  simp only [Pi.sub_apply, annih, creat, LinearMap.coe_mk, AddHom.coe_mk,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [← mul_assoc, sqrt_succ_sq]
  cases n with
  | zero => simp
  | succ m =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [← mul_assoc, sqrt_succ_sq]
      ring

/-- The number operator acts diagonally: `(N v) n = n * v n`. -/
theorem number_apply (v : Fock) (n : ℕ) : number v n = (n : ℂ) * v n := by
  cases n with
  | zero => simp [number, creat, annih]
  | succ m =>
      simp only [number, LinearMap.coe_comp, Function.comp_apply, creat, annih,
        LinearMap.coe_mk, AddHom.coe_mk, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [← mul_assoc, sqrt_succ_sq]

/-- The Hamiltonian acts diagonally: `(H v) n = ℏω (n + 1/2) * v n`. -/
theorem hamiltonian_apply (hbar omega : ℝ) (v : Fock) (n : ℕ) :
    hamiltonian hbar omega v n = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2) * v n := by
  simp only [hamiltonian, LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply,
    Pi.add_apply, LinearMap.id_coe, id_eq, smul_eq_mul, number_apply]
  ring

/-! ## Ladder operator structure -/

/-- The ground state is annihilated by `a`. -/
theorem annih_ground : annih (fockBasis 0) = 0 := by
  funext n
  simp [annih, fockBasis]

/-- Raising: `a† |n⟩ = √(n+1) |n+1⟩`. -/
theorem creat_basis (n : ℕ) :
    creat (fockBasis n) = ((Real.sqrt ((n : ℝ) + 1) : ℂ)) • fockBasis (n + 1) := by
  funext m
  cases m with
  | zero => simp [creat, fockBasis]
  | succ k =>
      simp only [creat, fockBasis, LinearMap.coe_mk, AddHom.coe_mk, Nat.add_sub_cancel,
        Pi.smul_apply, smul_eq_mul]
      by_cases h : k = n
      · subst h; simp
      · simp only [Nat.cast_add, Nat.cast_one, if_neg h,
          if_neg (fun hk : k + 1 = n + 1 => h (Nat.succ_injective hk)), mul_zero]

/-- Lowering: `a |n+1⟩ = √(n+1) |n⟩`. -/
theorem annih_basis_succ (n : ℕ) :
    annih (fockBasis (n + 1)) = ((Real.sqrt ((n : ℝ) + 1) : ℂ)) • fockBasis n := by
  funext m
  simp only [annih, fockBasis, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  by_cases h : m = n
  · subst h; simp
  · simp only [if_neg h, if_neg (fun hm : m + 1 = n + 1 => h (Nat.succ_injective hm)),
      mul_zero]

/-- The number states are obtained from the ground state by repeated raising:
    `(a†)^n |0⟩ = √(n!) |n⟩`. -/
theorem creat_pow_ground (n : ℕ) :
    (creat ^ n) (fockBasis 0) = ((Real.sqrt (n ! : ℝ) : ℂ)) • fockBasis n := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, creat_basis, smul_smul,
        ← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
      congr 2
      rw [Nat.factorial_succ]
      push_cast
      rw [mul_comm]

/-- Each number state is an eigenstate of the Hamiltonian with energy `ℏω(n + 1/2)`. -/
theorem hamiltonian_eigenstate (hbar omega : ℝ) (n : ℕ) :
    hamiltonian hbar omega (fockBasis n)
      = ((hbar * omega * ((n : ℝ) + 1 / 2) : ℝ) : ℂ) • fockBasis n := by
  funext m
  rw [hamiltonian_apply]
  simp only [fockBasis, Pi.smul_apply, smul_eq_mul]
  by_cases h : m = n
  · subst h; push_cast; ring
  · simp [h]

/-! ## The spectrum -/

/-- **Spectrum of the quantum harmonic oscillator.**  For the Hamiltonian
`H = ℏω (a† a + 1/2)` built from the ladder operators `a`, `a†` on Fock space, the set of
eigenvalues of `H` is exactly `{ℏω (n + 1/2) : n ∈ ℕ}`. -/
theorem oscillator_spectrum (hbar omega : ℝ) :
    {lam : ℂ | ∃ v : Fock, v ≠ 0 ∧ hamiltonian hbar omega v = lam • v}
      = {lam : ℂ | ∃ n : ℕ, lam = ((hbar * omega * ((n : ℝ) + 1 / 2) : ℝ) : ℂ)} := by
  ext lam
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, hHv⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, v n ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (funext fun n => by simpa using h n)
    refine ⟨n, ?_⟩
    have h := congrFun hHv n
    rw [hamiltonian_apply] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    have := mul_right_cancel₀ hn h
    rw [← this]
    push_cast
    ring
  · rintro ⟨n, rfl⟩
    refine ⟨fockBasis n, ?_, hamiltonian_eigenstate hbar omega n⟩
    intro h
    have := congrFun h n
    simp [fockBasis] at this

end QPhys

#print axioms QPhys.oscillator_spectrum
#print axioms QPhys.commutator_annih_creat
#print axioms QPhys.hamiltonian_eigenstate
#print axioms QPhys.creat_pow_ground
#print axioms QPhys.number_apply
#print axioms QPhys.hamiltonian_apply
#print axioms QPhys.annih_ground
#print axioms QPhys.creat_basis
#print axioms QPhys.annih_basis_succ

