import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Statement: Erasing one bit dissipates at least kT ln 2 of heat (Landauer).
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

namespace Phys

/-- The Gibbs (Boltzmann–Shannon) entropy `S = -k ∑ᵢ pᵢ log pᵢ` of a probability
distribution `p` on a finite set of microstates, with Boltzmann constant `k`. -/
noncomputable def gibbsEntropy {ι : Type*} [Fintype ι] (k : ℝ) (p : ι → ℝ) : ℝ :=
  -k * ∑ i, p i * Real.log (p i)

/-- The entropy of the uniform distribution on a nonempty finite set of `N` microstates
is `k log N` (Boltzmann's formula). -/
theorem gibbsEntropy_uniform {ι : Type*} [Fintype ι] [Nonempty ι] (k : ℝ) (p : ι → ℝ)
    (hp : ∀ i, p i = (Fintype.card ι : ℝ)⁻¹) :
    gibbsEntropy k p = k * Real.log (Fintype.card ι) := by
  have hne : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [gibbsEntropy, hp, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [Real.log_inv]
  field_simp

/-- A deterministic (point-mass) distribution has zero entropy. -/
theorem gibbsEntropy_dirac {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℝ) (i₀ : ι)
    (p : ι → ℝ) (hp : ∀ i, p i = if i = i₀ then 1 else 0) :
    gibbsEntropy k p = 0 := by
  have h : ∀ i : ι,
      (if i = i₀ then (1 : ℝ) else 0) * Real.log (if i = i₀ then (1 : ℝ) else 0) = 0 := by
    intro i
    by_cases hi : i = i₀ <;> simp [hi]
  simp only [gibbsEntropy, hp, h]
  simp

/--
**Landauer's principle.**

A memory bit is modelled as a two-state system (`Bool`) with Boltzmann constant `k`,
in contact with a heat bath at temperature `T > 0`.  Initially the bit is unknown, i.e.
its distribution `pInit` is uniform; after the erasure operation the bit is in a definite
state `b₀`, i.e. the distribution `pFinal` is the point mass at `b₀`.

The only physical input is the second law of thermodynamics in the form
`ΔS_total = ΔS_system + Q/T ≥ 0`, where `Q` is the heat dissipated into the bath.

Conclusion: the dissipated heat satisfies `Q ≥ k T log 2`, i.e. at least `kT ln 2`
of heat is released when one bit of information is erased.
-/
theorem landauer_principle
    (k T Q : ℝ) (hT : 0 < T)
    (pInit pFinal : Bool → ℝ)
    (hInit : ∀ b, pInit b = 1 / 2)
    (b₀ : Bool) (hFinal : ∀ b, pFinal b = if b = b₀ then 1 else 0)
    (hSecondLaw : 0 ≤ (gibbsEntropy k pFinal - gibbsEntropy k pInit) + Q / T) :
    k * T * Real.log 2 ≤ Q := by
  have hcard : (Fintype.card Bool : ℝ) = 2 := by simp
  have hSi : gibbsEntropy k pInit = k * Real.log 2 := by
    have := gibbsEntropy_uniform (ι := Bool) k pInit (by
      intro b; rw [hInit b, hcard]; norm_num)
    rwa [hcard] at this
  have hSf : gibbsEntropy k pFinal = 0 := gibbsEntropy_dirac k b₀ pFinal hFinal
  rw [hSi, hSf] at hSecondLaw
  -- `0 ≤ -(k log 2) + Q/T`, hence `k log 2 ≤ Q/T`, hence `k T log 2 ≤ Q`.
  have hQT : k * Real.log 2 ≤ Q / T := by linarith
  have := mul_le_mul_of_nonneg_left hQT (le_of_lt hT)
  rw [mul_div_cancel₀ _ (ne_of_gt hT)] at this
  linarith [this]

/--
**Landauer's principle for `n` bits.**

Erasing an `n`-bit register (uniform over its `2 ^ n` states, reset to a single definite
state) dissipates at least `n · k T log 2` of heat.
-/
theorem landauer_principle_nbits
    (n : ℕ) (k T Q : ℝ) (hT : 0 < T)
    (pInit pFinal : Fin (2 ^ n) → ℝ)
    (hInit : ∀ i, pInit i = ((2 : ℝ) ^ n)⁻¹)
    (i₀ : Fin (2 ^ n)) (hFinal : ∀ i, pFinal i = if i = i₀ then 1 else 0)
    (hSecondLaw : 0 ≤ (gibbsEntropy k pFinal - gibbsEntropy k pInit) + Q / T) :
    (n : ℝ) * (k * T * Real.log 2) ≤ Q := by
  haveI : Nonempty (Fin (2 ^ n)) := ⟨i₀⟩
  have hcard : (Fintype.card (Fin (2 ^ n)) : ℝ) = (2 : ℝ) ^ n := by
    simp
  have hSi : gibbsEntropy k pInit = (n : ℝ) * (k * Real.log 2) := by
    have h := gibbsEntropy_uniform (ι := Fin (2 ^ n)) k pInit (by
      intro i; rw [hInit i, hcard])
    rw [hcard, Real.log_pow] at h
    rw [h]; ring
  have hSf : gibbsEntropy k pFinal = 0 := gibbsEntropy_dirac k i₀ pFinal hFinal
  rw [hSi, hSf] at hSecondLaw
  have hQT : (n : ℝ) * (k * Real.log 2) ≤ Q / T := by linarith
  have h2 := mul_le_mul_of_nonneg_left hQT (le_of_lt hT)
  rw [mul_div_cancel₀ _ (ne_of_gt hT)] at h2
  nlinarith [h2]

end Phys

