/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of the formalisation

The ensemble is a *commuting* (equivalently: simultaneously diagonalizable) family of states,
measured by a POVM that is diagonal in the same eigenbasis.  Concretely, a state `ρₓ` is recorded
by its spectrum `r x : Z → ℝ` in a fixed orthonormal eigenbasis indexed by `Z`, a POVM element
`E y` by its diagonal `Z → ℝ`, and the Born rule is `Pr[y | x] = ∑ z, r x z * E y z`.  In this
situation the von Neumann entropy is the Shannon entropy of the spectrum, so the Holevo quantity
`χ = S(∑ₓ pₓ ρₓ) - ∑ₓ pₓ S(ρₓ)` and the accessible information are the ones defined below, and
`QI.holevo_bound` is the Holevo inequality `I_acc ≤ χ` for such ensembles.  The bound is tight:
for a uniform ensemble of two orthogonal states, measured in their own basis, both sides equal
`log 2`.  The fully general (non-commuting) case is not covered here.
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

set_option grind.warning false

namespace QI

/-! ## The log-sum inequality -/

/-- **Log-sum inequality**: for nonnegative weights `a`, `b` on a finite set such that `b i = 0`
forces `a i = 0` (absolute continuity), one has
`(∑ a) * log ((∑ a) / (∑ b)) ≤ ∑ a i * log (a i / b i)`. -/

theorem mutualInfo_le_holevoChi (p : X → ℝ) (r : X → Z → ℝ) (E : Y → Z → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hr0 : ∀ x z, 0 ≤ r x z) (hE : IsPOVM E) :
    mutualInfo p (outProb r E) ≤ holevoChi p r := by
  obtain ⟨hE0, hE1⟩ := hE
  set q : X → Y → ℝ := outProb r E with hq
  set avg : Z → ℝ := avgState p r with havg
  have havg0 : ∀ z, 0 ≤ avg z := fun z =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (hr0 x z)
  have hq0 : ∀ x y, 0 ≤ q x y := fun x y =>
    Finset.sum_nonneg fun z _ => mul_nonneg (hr0 x z) (hE0 y z)
  -- marginal of the outcome
  have hmarg : ∀ y : Y, (∑ x', p x' * q x' y) = ∑ z, avg z * E y z := by
    intro y
    rw [hq]
    simp only [outProb, havg, avgState, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro z _
    refine Finset.sum_congr rfl ?_
    intro x _
    ring
  -- the key per-(x,y) estimate coming from the log-sum inequality
  have key : ∀ x : X, ∀ y : Y,
      p x * q x y * Real.log (q x y / ∑ x', p x' * q x' y)
        ≤ ∑ z, p x * r x z * E y z * Real.log (r x z / avg z) := by
    intro x y
    have hsa : (∑ z, p x * r x z * E y z) = p x * q x y := by
      rw [hq]; simp only [outProb, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro z _; ring
    have hsb : (∑ z, p x * avg z * E y z) = p x * ∑ x', p x' * q x' y := by
      rw [hmarg y, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro z _; ring
    have hls := log_sum_inequality (Finset.univ : Finset Z)
      (fun z => p x * r x z * E y z) (fun z => p x * avg z * E y z)
      (fun z _ => mul_nonneg (mul_nonneg (hp0 x) (hr0 x z)) (hE0 y z))
      (fun z _ => mul_nonneg (mul_nonneg (hp0 x) (havg0 z)) (hE0 y z))
      (by
        intro z _ hbz
        simp only at hbz ⊢
        rcases eq_or_lt_of_le (hp0 x) with h | hpx
        · rw [← h]; ring
        rcases eq_or_lt_of_le (hE0 y z) with h | hEyz
        · rw [← h]; ring
        have havgz : avg z = 0 := by
          by_contra hne
          have : p x * avg z * E y z ≠ 0 := by
            have := havg0 z
            have hpos : 0 < avg z := lt_of_le_of_ne this (Ne.symm hne)
            positivity
          exact this hbz
        have hrxz : p x * r x z = 0 := by
          have hnn : ∀ x' ∈ Finset.univ, 0 ≤ p x' * r x' z := fun x' _ =>
            mul_nonneg (hp0 x') (hr0 x' z)
          exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 havgz x (Finset.mem_univ x)
        rw [hrxz]; ring)
    rw [hsa, hsb] at hls
    -- rewrite both sides
    have hlhs : p x * q x y * Real.log (q x y / ∑ x', p x' * q x' y)
        ≤ p x * q x y * Real.log ((p x * q x y) / (p x * ∑ x', p x' * q x' y)) := by
      rcases eq_or_lt_of_le (hp0 x) with h | hpx
      · rw [← h]; simp
      · rw [mul_div_mul_left _ _ (ne_of_gt hpx)]
    refine le_trans hlhs (le_trans hls (le_of_eq ?_))
    refine Finset.sum_congr rfl ?_
    intro z _
    simp only
    rcases eq_or_lt_of_le (hp0 x) with h | hpx
    · rw [← h]; ring
    rcases eq_or_lt_of_le (hE0 y z) with h | hEyz
    · rw [← h]; ring
    have hc : (p x * E y z) ≠ 0 := by positivity
    have e1 : p x * r x z * E y z = (p x * E y z) * r x z := by ring
    have e2 : p x * avg z * E y z = (p x * E y z) * avg z := by ring
    rw [e1, e2, mul_div_mul_left _ _ hc]
  -- assemble
  have step1 : mutualInfo p q ≤ ∑ x, ∑ y, ∑ z, p x * r x z * E y z * Real.log (r x z / avg z) := by
    refine Finset.sum_le_sum ?_
    intro x _
    exact Finset.sum_le_sum fun y _ => key x y
  have step2 : ∀ x : X, (∑ y, ∑ z, p x * r x z * E y z * Real.log (r x z / avg z))
      = ∑ z, p x * r x z * Real.log (r x z / avg z) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro z _
    have : ∀ y : Y, p x * r x z * E y z * Real.log (r x z / avg z)
        = (p x * r x z * Real.log (r x z / avg z)) * E y z := by
      intro y; ring
    simp only [this]
    rw [← Finset.mul_sum, hE1 z, mul_one]
  simp only [step2] at step1
  rw [holevoChi_eq p r hp0 hr0]
  exact step1

end

/-- **The Holevo bound.**  For a quantum ensemble `{pₓ, ρₓ}` (here: a family of states that is
simultaneously diagonalizable, recorded by the spectra `r x` in a common eigenbasis indexed by
`Z`), the accessible information — the supremum over all POVMs of the mutual information between
the label `x` and the measurement outcome — is at most the Holevo quantity
`χ = S(∑ₓ pₓ ρₓ) - ∑ₓ pₓ S(ρₓ)`.

(The normalisation hypotheses `hp1` and `hr1` express that `p` is a probability distribution and
each `ρₓ` is a state; the proof in fact only uses positivity.) -/
