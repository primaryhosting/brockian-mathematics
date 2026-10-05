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

/-!
## The Fock space model of the quantum harmonic oscillator

We realise the state space of the one-dimensional quantum harmonic oscillator as the
(algebraic) Fock space `ℕ →₀ ℂ`, whose canonical basis vector `Finsupp.single n 1`
represents the `n`-th number state `|n⟩`.

The ladder operators are defined on this basis by the usual formulas
`a |n⟩ = √n |n-1⟩` and `a† |n⟩ = √(n+1) |n+1⟩`; we check the canonical commutation
relation `[a, a†] = 1`, build the number operator `N = a† a` and the Hamiltonian
`H = ℏω (N + ½)`, and finally compute the set of eigenvalues of `H` to be exactly
`{ℏω(n + ½) : n ∈ ℕ}`.
-/

/-- The annihilation (lowering) operator `a`, determined by `a |n⟩ = √n |n-1⟩`. -/
noncomputable def ladderDown : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n => LinearMap.toSpanSingleton ℂ _ (Finsupp.single (n - 1) (Real.sqrt n : ℂ))

/-- The creation (raising) operator `a†`, determined by `a† |n⟩ = √(n+1) |n+1⟩`. -/
noncomputable def ladderUp : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n =>
    LinearMap.toSpanSingleton ℂ _ (Finsupp.single (n + 1) (Real.sqrt (n + 1) : ℂ))

@[simp]
lemma ladderDown_single (n : ℕ) (c : ℂ) :
    ladderDown (Finsupp.single n c) = Finsupp.single (n - 1) (c * Real.sqrt n) := by
  simp [ladderDown, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.smul_single]

@[simp]
lemma ladderUp_single (n : ℕ) (c : ℂ) :
    ladderUp (Finsupp.single n c) = Finsupp.single (n + 1) (c * Real.sqrt (n + 1)) := by
  simp [ladderUp, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.smul_single]

private lemma sqrt_mul_self_cast (m : ℕ) :
    ((Real.sqrt ((m : ℝ) + 1) : ℂ)) * ((Real.sqrt ((m : ℝ) + 1) : ℂ)) = (m : ℂ) + 1 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

/-- The number operator `N = a† a`. -/
noncomputable def numberOp : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) := ladderUp ∘ₗ ladderDown

lemma numberOp_single (n : ℕ) (c : ℂ) :
    numberOp (Finsupp.single n c) = Finsupp.single n (c * n) := by
  cases n with
  | zero => simp [numberOp]
  | succ m =>
      simp only [numberOp, LinearMap.coe_comp, Function.comp_apply, ladderDown_single,
        ladderUp_single, Nat.succ_sub_one]
      congr 1
      push_cast [mul_assoc, sqrt_mul_self_cast]
      ring

/-- The number operator is diagonal: `(N v) m = m * v m`. -/
lemma numberOp_apply (v : ℕ →₀ ℂ) (m : ℕ) : (numberOp v) m = (m : ℂ) * v m := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]; ring
  | single a b =>
      rw [numberOp_single]
      by_cases h : a = m
      · subst h; simp [mul_comm]
      · simp [h]

lemma ladderDown_ladderUp_apply (v : ℕ →₀ ℂ) (m : ℕ) :
    (ladderDown (ladderUp v)) m = ((m : ℂ) + 1) * v m := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]; ring
  | single a b =>
      rw [ladderUp_single, ladderDown_single]
      simp only [Nat.add_sub_cancel]
      by_cases h : a = m
      · subst h
        rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
        push_cast [mul_assoc, sqrt_mul_self_cast]
        ring
      · simp [h]

/-- The canonical commutation relation `[a, a†] = 1`. -/
theorem ladder_commutator :
    ladderDown ∘ₗ ladderUp - ladderUp ∘ₗ ladderDown = LinearMap.id := by
  refine LinearMap.ext fun v => Finsupp.ext fun m => ?_
  have hN : (ladderUp (ladderDown v)) m = (m : ℂ) * v m := numberOp_apply v m
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply,
    Finsupp.sub_apply, ladderDown_ladderUp_apply, hN]
  ring

/-- The Hamiltonian of the quantum harmonic oscillator, `H = ℏω (a† a + ½)`. -/
noncomputable def hamiltonian (hbar omega : ℝ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  ((hbar * omega : ℝ) : ℂ) • (numberOp + (1 / 2 : ℂ) • LinearMap.id)

lemma hamiltonian_apply (hbar omega : ℝ) (v : ℕ →₀ ℂ) (m : ℕ) :
    (hamiltonian hbar omega v) m = ((hbar * omega * (m + 1 / 2) : ℝ) : ℂ) * v m := by
  simp only [hamiltonian, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul, numberOp_apply]
  push_cast
  ring

/-- Each number state `|n⟩` is an eigenvector of `H` with eigenvalue `ℏω(n + ½)`. -/
theorem hamiltonian_numberState (hbar omega : ℝ) (n : ℕ) :
    hamiltonian hbar omega (Finsupp.single n 1) =
      ((hbar * omega * (n + 1 / 2) : ℝ) : ℂ) • (Finsupp.single n (1 : ℂ)) := by
  ext m
  rw [hamiltonian_apply]
  by_cases h : n = m
  · subst h; simp
  · simp [h]

/-- **Spectrum of the quantum harmonic oscillator.**

In the Fock-space model built from the ladder operators `a`, `a†` (which satisfy
`[a, a†] = 1`, see `QPhys.ladder_commutator`), the set of eigenvalues of the Hamiltonian
`H = ℏω (a† a + ½)` is exactly `{ℏω (n + ½) : n ∈ ℕ}`. -/
theorem oscillator_spectrum (hbar omega : ℝ) :
    {lam : ℂ | ∃ v : ℕ →₀ ℂ, v ≠ 0 ∧ hamiltonian hbar omega v = lam • v} =
      {lam : ℂ | ∃ n : ℕ, lam = ((hbar * omega * (n + 1 / 2) : ℝ) : ℂ)} := by
  ext lam
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, hEig⟩
    obtain ⟨m, hm⟩ : ∃ m, v m ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hv (Finsupp.ext hcon)
    refine ⟨m, ?_⟩
    have h := congrArg (fun w => w m) hEig
    simp only [hamiltonian_apply, Finsupp.smul_apply, smul_eq_mul] at h
    exact (mul_right_cancel₀ hm h).symm
  · rintro ⟨n, rfl⟩
    exact ⟨Finsupp.single n 1, by simp, hamiltonian_numberState hbar omega n⟩

/-- **Non-degeneracy of the spectrum.** For `ℏω ≠ 0`, every eigenvector of `H` with
eigenvalue `ℏω (n + ½)` is a multiple of the number state `|n⟩`. -/
theorem eigenvector_eq_smul_numberState (hbar omega : ℝ) (hne : hbar * omega ≠ 0) (n : ℕ)
    (v : ℕ →₀ ℂ) (hEig : hamiltonian hbar omega v = ((hbar * omega * (n + 1 / 2) : ℝ) : ℂ) • v) :
    v = (v n) • (Finsupp.single n (1 : ℂ)) := by
  refine Finsupp.ext fun m => ?_
  have h := congrArg (fun w => w m) hEig
  simp only [hamiltonian_apply, Finsupp.smul_apply, smul_eq_mul] at h
  by_cases hm : m = n
  · subst hm; simp
  · have hcoef : ((hbar * omega * (m + 1 / 2) : ℝ) : ℂ) ≠ ((hbar * omega * (n + 1 / 2) : ℝ) : ℂ) := by
      simp only [ne_eq, Complex.ofReal_inj]
      intro hEq
      have h2 : ((m : ℝ) + 1 / 2) = ((n : ℝ) + 1 / 2) := mul_left_cancel₀ hne hEq
      exact hm (by exact_mod_cast (by linarith : (m : ℝ) = n))
    have : v m = 0 := by
      by_contra hv
      exact hcoef (mul_right_cancel₀ hv h)
    simp [this, hm]

end QPhys

