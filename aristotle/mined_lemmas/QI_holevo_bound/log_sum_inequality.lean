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

theorem log_sum_inequality {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hac : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  set A := ∑ i ∈ s, a i with hA
  set B := ∑ i ∈ s, b i with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg ha
  have hB0 : 0 ≤ B := Finset.sum_nonneg hb
  rcases eq_or_lt_of_le hA0 with hA' | hApos
  · -- A = 0 : every `a i = 0`
    have hzero : ∀ i ∈ s, a i = 0 := by
      intro i hi
      have := (Finset.sum_eq_zero_iff_of_nonneg ha).1 hA'.symm i hi
      exact this
    have h1 : A * Real.log (A / B) = 0 := by rw [← hA']; ring
    rw [h1]
    refine le_of_eq ?_
    symm
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [hzero i hi]; ring
  · have hBpos : 0 < B := by
      rcases eq_or_lt_of_le hB0 with hB' | h
      · exfalso
        have hzero : ∀ i ∈ s, b i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hb).1 hB'.symm
        have : A = 0 := by
          rw [hA]
          exact Finset.sum_eq_zero fun i hi => hac i hi (hzero i hi)
        exact absurd this (ne_of_gt hApos)
      · exact h
    -- pointwise bound
    have key : ∀ i ∈ s, a i * Real.log (A / B) + (a i - A * b i / B)
        ≤ a i * Real.log (a i / b i) := by
      intro i hi
      rcases eq_or_lt_of_le (ha i hi) with hai | haipos
      · -- a i = 0
        have hai' : a i = 0 := hai.symm
        rw [hai']
        have : 0 ≤ A * b i / B := div_nonneg (mul_nonneg hA0 (hb i hi)) hB0
        simp only [zero_mul, zero_sub, zero_add]
        linarith
      · have hbipos : 0 < b i := by
          rcases eq_or_lt_of_le (hb i hi) with hbi | h
          · exact absurd (hac i hi hbi.symm) (ne_of_gt haipos)
          · exact h
        set t := (a i * B) / (b i * A) with ht
        have htpos : 0 < t := by
          rw [ht]; positivity
        have hlog : Real.log (1 / t) ≤ 1 / t - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have hlogt : 1 - 1 / t ≤ Real.log t := by
          rw [Real.log_div one_ne_zero (ne_of_gt htpos)] at hlog
          simp only [Real.log_one, zero_sub] at hlog
          linarith
        have hinvt : 1 / t = (b i * A) / (a i * B) := by
          rw [ht]; rw [one_div, inv_div]
        have hlogsplit : Real.log t = Real.log (a i / b i) - Real.log (A / B) := by
          rw [ht]
          rw [show (a i * B) / (b i * A) = (a i / b i) / (A / B) by field_simp]
          rw [Real.log_div (by positivity) (by positivity)]
        have h1 : a i * (1 - 1 / t) ≤ a i * Real.log t := by
          exact mul_le_mul_of_nonneg_left hlogt (le_of_lt haipos)
        have h2 : a i * (1 - 1 / t) = a i - A * b i / B := by
          rw [hinvt]
          field_simp
        rw [h2, hlogsplit] at h1
        linarith
    have hsum := Finset.sum_le_sum key
    have hleft : ∑ i ∈ s, (a i * Real.log (A / B) + (a i - A * b i / B))
        = A * Real.log (A / B) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]
      have : ∑ i ∈ s, A * b i / B = A := by
        rw [show (fun i => A * b i / B) = (fun i => (A / B) * b i) by
          funext i; ring]
        rw [← Finset.mul_sum, ← hB]
        field_simp
      rw [this, ← hA]
      ring
    rw [hleft] at hsum
    exact hsum

/-! ## Ensembles, POVMs and the entropic quantities

We work with a family of states that is simultaneously diagonal in a fixed orthonormal basis
indexed by `Z`, together with a POVM that is diagonal in the same basis.  A state is therefore
recorded by its spectrum `r x : Z → ℝ` (a probability vector, i.e. the diagonal of the density
matrix), and a POVM by its diagonal entries `E y : Z → ℝ`.  In this commuting situation the von
Neumann entropy of a state is the Shannon entropy of its spectrum, the Born rule reads
`Pr[y | x] = ∑ z, r x z * E y z`, and the Holevo quantity is
`χ = S(∑ₓ pₓ ρₓ) - ∑ₓ pₓ S(ρₓ)` as usual. -/

variable {X Y Z : Type*}

/-- Shannon (= von Neumann, in the common eigenbasis) entropy of a spectrum `r`. -/
