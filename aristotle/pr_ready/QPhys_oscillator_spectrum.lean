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

(Lean requires `import` commands to precede every other command, including module
documentation, so the header comment above is a plain block comment.)

We realise the one-dimensional quantum harmonic oscillator algebraically on the Fock space
`ℕ →₀ ℂ`, whose basis vector `Finsupp.single n 1` is the number state `|n⟩`.  The ladder
operators `a` (`QPhys.ann`) and `a†` (`QPhys.cre`) satisfy the canonical commutation
relation `[a, a†] = 1`, the number operator `N = a† a` acts diagonally, and the Hamiltonian
`H = ℏω (a†a + ½)` has eigenvalues exactly `ℏω(n + ½)`, `n ∈ ℕ`.
-/

namespace QPhys

/-! ## Ladder operators -/

/-- The annihilation (lowering) operator, `a |n⟩ = √n |n-1⟩`.  For `n = 0` the prefactor
`√0 = 0` vanishes, so `|0⟩` is the vacuum. -/
noncomputable def ann : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n => LinearMap.toSpanSingleton ℂ _ (Finsupp.single (n - 1) (Real.sqrt n : ℂ))

/-- The creation (raising) operator, `a† |n⟩ = √(n+1) |n+1⟩`. -/
noncomputable def cre : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n =>
    LinearMap.toSpanSingleton ℂ _ (Finsupp.single (n + 1) (Real.sqrt (n + 1) : ℂ))

/-- The number operator `N = a† a`. -/
noncomputable def numOp : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) := cre ∘ₗ ann

/-- The Hamiltonian of the harmonic oscillator, `H = ℏω (a† a + ½)`. -/
noncomputable def hamiltonian (hbar omega : ℝ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  ((hbar * omega : ℝ) : ℂ) • (numOp + (1 / 2 : ℂ) • LinearMap.id)

@[simp] lemma ann_single (n : ℕ) (c : ℂ) :
    ann (Finsupp.single n c) = c • Finsupp.single (n - 1) (Real.sqrt n : ℂ) := by
  simp [ann, LinearMap.toSpanSingleton_apply]

@[simp] lemma cre_single (n : ℕ) (c : ℂ) :
    cre (Finsupp.single n c) = c • Finsupp.single (n + 1) (Real.sqrt (n + 1) : ℂ) := by
  simp [cre, LinearMap.toSpanSingleton_apply]

private lemma sqrt_mul_sqrt_succ (m : ℕ) :
    ((Real.sqrt (m + 1) : ℂ)) * (Real.sqrt (m + 1) : ℂ) = ((m : ℂ) + 1) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast; ring

/-! ## The number operator is diagonal -/

/-- `a† a` is diagonal in the number basis: `(N v) n = n * v n`. -/
theorem numOp_apply (v : ℕ →₀ ℂ) (n : ℕ) : (numOp v) n = (n : ℂ) * v n := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]; ring
  | single a b =>
      rw [numOp, LinearMap.comp_apply, ann_single, map_smul, cre_single]
      rcases a with _ | m
      · simp only [Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, Finsupp.single_apply]
        push_cast
        split_ifs with h <;> simp [h]
      · simp only [Nat.add_sub_cancel, Finsupp.smul_single, Finsupp.single_apply, smul_eq_mul]
        split_ifs with h
        · subst h
          push_cast
          linear_combination b * sqrt_mul_sqrt_succ m
        · ring

/-- `a a†` is diagonal in the number basis: `(a a† v) n = (n+1) * v n`. -/
theorem ann_cre_apply (v : ℕ →₀ ℂ) (n : ℕ) : (ann (cre v)) n = ((n : ℂ) + 1) * v n := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]; ring
  | single a b =>
      rw [cre_single, map_smul, ann_single]
      simp only [Nat.add_sub_cancel, Finsupp.smul_single, Finsupp.single_apply, smul_eq_mul]
      split_ifs with h
      · subst h
        push_cast
        linear_combination b * sqrt_mul_sqrt_succ a
      · ring

/-- The canonical commutation relation `[a, a†] = 1`. -/
theorem commutator_ann_cre : ann ∘ₗ cre - cre ∘ₗ ann = LinearMap.id := by
  refine LinearMap.ext fun v => Finsupp.ext fun k => ?_
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
    id_eq, Finsupp.sub_apply]
  rw [ann_cre_apply, show cre (ann v) = numOp v from rfl, numOp_apply]
  ring

/-- `N |n⟩ = n |n⟩`. -/
theorem numOp_single (n : ℕ) (c : ℂ) :
    numOp (Finsupp.single n c) = (n : ℂ) • Finsupp.single n c := by
  refine Finsupp.ext fun k => ?_
  rw [numOp_apply, Finsupp.smul_apply, smul_eq_mul]
  rcases eq_or_ne n k with rfl | h
  · rfl
  · rw [Finsupp.single_apply, if_neg h]; ring

/-! ## Ladder construction of the eigenstates -/

/-- The vacuum `|0⟩` is annihilated by `a`. -/
theorem ann_vacuum : ann (Finsupp.single 0 (1 : ℂ)) = 0 := by simp

/-- The `n`-th excited state is produced from the vacuum by the raising operator:
`(a†)^n |0⟩ = √(n!) |n⟩`. -/
theorem cre_pow_vacuum (n : ℕ) :
    (cre ^ n) (Finsupp.single 0 (1 : ℂ)) = Finsupp.single n ((Real.sqrt n.factorial : ℂ)) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', show ((cre * cre ^ m) (Finsupp.single 0 (1 : ℂ)))
            = cre ((cre ^ m) (Finsupp.single 0 (1 : ℂ))) from rfl, ih, cre_single, Finsupp.smul_single, smul_eq_mul]
      congr 1
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul (Nat.cast_nonneg _)]
      norm_cast
      rw [Nat.factorial_succ]
      push_cast
      rw [mul_comm]

/-- The energy eigenstates: `H |n⟩ = ℏω (n + ½) |n⟩`. -/
theorem hamiltonian_eigenstate (hbar omega : ℝ) (n : ℕ) (c : ℂ) :
    hamiltonian hbar omega (Finsupp.single n c)
      = (((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2)) • Finsupp.single n c := by
  rw [hamiltonian]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_coe, id_eq, numOp_single,
    LinearMap.smul_apply]
  rw [← add_smul, smul_smul]

/-! ## The spectrum -/

/-- **Spectrum of the quantum harmonic oscillator.**
A complex number `lam` is an eigenvalue of the harmonic-oscillator Hamiltonian
`H = ℏω (a†a + ½)` on the Fock space `ℕ →₀ ℂ` if and only if `lam = ℏω (n + ½)` for some
natural number `n`; that is, the spectrum is exactly `{ℏω(n + ½) : n ∈ ℕ}`.  The eigenvector
for the level `n` is the ladder-operator state `(a†)^n |0⟩` (see `QPhys.cre_pow_vacuum`). -/
theorem oscillator_spectrum (hbar omega : ℝ) (lam : ℂ) :
    (∃ v : ℕ →₀ ℂ, v ≠ 0 ∧ hamiltonian hbar omega v = lam • v) ↔
      ∃ n : ℕ, lam = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2) := by
  constructor
  · rintro ⟨v, hv, hEq⟩
    obtain ⟨n, hn⟩ := Finsupp.support_nonempty_iff.mpr hv
    refine ⟨n, ?_⟩
    have hvn : v n ≠ 0 := Finsupp.mem_support_iff.mp hn
    have h1 : (hamiltonian hbar omega v) n
        = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2) * v n := by
      rw [hamiltonian]
      simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_coe, id_eq,
        Finsupp.coe_smul, Pi.smul_apply, Finsupp.add_apply, smul_eq_mul, numOp_apply]
      ring
    have h2 : (hamiltonian hbar omega v) n = lam * v n := by
      rw [hEq]; simp
    exact (mul_right_cancel₀ hvn (h1.symm.trans h2)).symm
  · rintro ⟨n, rfl⟩
    exact ⟨Finsupp.single n 1, Finsupp.single_ne_zero.mpr one_ne_zero,
      hamiltonian_eigenstate hbar omega n 1⟩

end QPhys


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

