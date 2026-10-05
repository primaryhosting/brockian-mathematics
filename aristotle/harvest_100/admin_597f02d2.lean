/-
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Overview

This file formalises the Coffman–Kundu–Wootters (CKW) monogamy inequality for a
pure state of three qubits:

  τ(A|BC)  ≥  τ(A|B) + τ(A|C),

where `τ` denotes the *tangle* (the square of the concurrence).

A pure three qubit state is described by its amplitude tensor
`a : Bool → Bool → Bool → ℂ`, `|ψ⟩ = ∑_{x,y,z} a x y z • |xyz⟩`.

The three tangles are expressed by their standard closed forms:

* `tangleA a = 4 · det ρ_A`, the tangle of the bipartite split `A | BC`
  (for a pure bipartite state the squared concurrence equals
  `2(1 - tr ρ_A²) = 4 det ρ_A` for a qubit `A`).

* For the two qubit *mixed* reduced states `ρ_AB` and `ρ_AC` the tangle is the
  square of Wootters' concurrence `C = max(0, λ₁ - λ₂ - λ₃ - λ₄)`, the `λᵢ`
  being the decreasingly ordered singular values of `ρ` relative to the spin
  flip.  Since `ρ_AB = ∑_c |w_c⟩⟨w_c|` with `w_c = ∑_{x,y} a x y c • |xy⟩` has
  rank at most two, only two of the `λᵢ` can be nonzero, and they are the
  singular values of the symmetric `2 × 2` matrix

      `Mc a c c' = ⟨w_c|ᵀ (σ_y ⊗ σ_y) |w_{c'}⟩`

  (indeed the nonzero eigenvalues of `ρ ρ̃` are those of `M̄ M = M† M`).
  Consequently

      `C² = (λ₁ - λ₂)² = ‖M‖_F² - 2 |det M|`,

  which is the definition `tangleAB` below; `tangleAC` is the same with the
  roles of `B` and `C` exchanged (matrix `Mb`).

The whole content of the CKW inequality is then the polynomial identity

  `‖Mc‖_F² + ‖Mb‖_F² = 4 det ρ_A`     (`frob_sum_eq`)

together with `|det M| ≥ 0`.  The difference
`τ(A|BC) - τ(A|B) - τ(A|C) = 2|det Mc| + 2|det Mb|` is the residual
(three) tangle, recorded as `ckw_residual`.

No normalisation of the amplitudes is assumed: every quantity involved is
homogeneous of degree four in the amplitudes, so the inequality holds for an
arbitrary amplitude tensor.
-/

open Complex Finset

namespace QI

/-- Amplitude tensor of a three qubit state: `|ψ⟩ = ∑ a x y z • |xyz⟩`. -/
abbrev Amp := Bool → Bool → Bool → ℂ

/-- Entrywise complex conjugate of an amplitude tensor. -/
def conjAmp (a : Amp) : Amp := fun x y z => (starRingEnd ℂ) (a x y z)

/-- The symmetric `2 × 2` matrix `⟨w_c|ᵀ (σ_y ⊗ σ_y) |w_{c'}⟩`, where
`w_c = ∑_{x,y} a x y c • |xy⟩` spans the support of `ρ_AB`. -/
def Mc (a : Amp) (c c' : Bool) : ℂ :=
  -(a false false c * a true true c') + a false true c * a true false c'
  + a true false c * a false true c' - a true true c * a false false c'

/-- The analogous matrix for the pair `A C`: `w'_b = ∑_{x,z} a x b z • |xz⟩`. -/
def Mb (a : Amp) (b b' : Bool) : ℂ :=
  -(a false b false * a true b' true) + a false b true * a true b' false
  + a true b false * a false b' true - a true b true * a false b' false

/-- Squared Frobenius norm of `Mc`, i.e. `λ₁² + λ₂²` for the pair `A B`. -/
noncomputable def frobC (a : Amp) : ℝ := ∑ c : Bool, ∑ c' : Bool, normSq (Mc a c c')

/-- Squared Frobenius norm of `Mb`, i.e. `λ₁² + λ₂²` for the pair `A C`. -/
noncomputable def frobB (a : Amp) : ℝ := ∑ b : Bool, ∑ b' : Bool, normSq (Mb a b b')

/-- Determinant of `Mc`; its modulus is the product `λ₁ λ₂` for the pair `A B`. -/
def detMc (a : Amp) : ℂ :=
  Mc a false false * Mc a true true - Mc a false true * Mc a true false

/-- Determinant of `Mb`; its modulus is the product `λ₁ λ₂` for the pair `A C`. -/
def detMb (a : Amp) : ℂ :=
  Mb a false false * Mb a true true - Mb a false true * Mb a true false

/-- Determinant of the reduced density matrix `ρ_A` of the first qubit. -/
noncomputable def detRhoA (a : Amp) : ℝ :=
  (∑ y : Bool, ∑ z : Bool, normSq (a false y z)) *
      (∑ y : Bool, ∑ z : Bool, normSq (a true y z))
    - normSq (∑ y : Bool, ∑ z : Bool, a false y z * (starRingEnd ℂ) (a true y z))

/-- The tangle of the bipartite split `A | BC`, equal to `4 det ρ_A`. -/
noncomputable def tangleA (a : Amp) : ℝ := 4 * detRhoA a

/-- The tangle (squared Wootters concurrence) of the reduced state `ρ_AB`. -/
noncomputable def tangleAB (a : Amp) : ℝ := frobC a - 2 * ‖detMc a‖

/-- The tangle (squared Wootters concurrence) of the reduced state `ρ_AC`. -/
noncomputable def tangleAC (a : Amp) : ℝ := frobB a - 2 * ‖detMb a‖

/-- Polarised form of the basic quartic identity: it is a polynomial identity in
the amplitudes `a` and an independent copy `b` (which will be `conjAmp a`). -/
lemma polarised_identity (a b : Amp) :
    ((Mc a false false * Mc b false false + Mc a false true * Mc b false true
      + Mc a true false * Mc b true false + Mc a true true * Mc b true true)
     + (Mb a false false * Mb b false false + Mb a false true * Mb b false true
      + Mb a true false * Mb b true false + Mb a true true * Mb b true true))
      = 4 * (((∑ y : Bool, ∑ z : Bool, a false y z * b false y z)
              * (∑ y : Bool, ∑ z : Bool, a true y z * b true y z))
        - (∑ y : Bool, ∑ z : Bool, a false y z * b true y z)
          * (∑ y : Bool, ∑ z : Bool, b false y z * a true y z)) := by
  simp only [Mc, Mb, Fintype.sum_bool]
  ring

lemma Mc_conjAmp (a : Amp) (c c' : Bool) :
    Mc (conjAmp a) c c' = (starRingEnd ℂ) (Mc a c c') := by
  simp [Mc, conjAmp]

lemma Mb_conjAmp (a : Amp) (b b' : Bool) :
    Mb (conjAmp a) b b' = (starRingEnd ℂ) (Mb a b b') := by
  simp [Mb, conjAmp]

/-- The key quartic identity: the two squared Frobenius norms add up to the
tangle of the split `A | BC`. -/
theorem frob_sum_eq (a : Amp) : frobC a + frobB a = 4 * detRhoA a := by
  have e1 : ∀ z : ℂ, ((normSq z : ℝ) : ℂ) = z * (starRingEnd ℂ) z :=
    fun z => (Complex.mul_conj z).symm
  have h := polarised_identity a (conjAmp a)
  simp only [Mc_conjAmp, Mb_conjAmp, conjAmp, Fintype.sum_bool] at h
  have hc : ((frobC a + frobB a : ℝ) : ℂ) = ((4 * detRhoA a : ℝ) : ℂ) := by
    simp only [frobC, frobB, detRhoA, Fintype.sum_bool]
    push_cast [e1, map_add, map_mul, RCLike.conj_conj]
    linear_combination h
  exact_mod_cast hc

/-- **CKW monogamy inequality** for a pure state of three qubits:
the tangle of the split `A | BC` dominates the sum of the two pairwise
tangles. -/
theorem monogamy_ckw (a : Amp) : tangleAB a + tangleAC a ≤ tangleA a := by
  have h := frob_sum_eq a
  have h1 : (0:ℝ) ≤ ‖detMc a‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖detMb a‖ := norm_nonneg _
  simp only [tangleAB, tangleAC, tangleA]
  linarith

/-- The residual (three-)tangle: the exact defect in the CKW inequality. -/
theorem ckw_residual (a : Amp) :
    tangleA a - (tangleAB a + tangleAC a) = 2 * ‖detMc a‖ + 2 * ‖detMb a‖ := by
  have h := frob_sum_eq a
  simp only [tangleAB, tangleAC, tangleA]
  linarith

/-!
## Sanity checks

The two paradigmatic three qubit states, in unnormalised form (rescaling the
amplitudes by `t` rescales every tangle by `|t|⁴`, so the values below are those
of the normalised states multiplied by `4`).
-/

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩`. -/
noncomputable def ghzAmp : Amp := fun x y z => if x = y ∧ y = z then 1 else 0

/-- The (unnormalised) W state `|100⟩ + |010⟩ + |001⟩`. -/
noncomputable def wAmp : Amp := fun x y z =>
  if (x ∧ !y ∧ !z) ∨ (!x ∧ y ∧ !z) ∨ (!x ∧ !y ∧ z) then 1 else 0

example : tangleA ghzAmp = 4 := by
  simp only [tangleA, detRhoA, Fintype.sum_bool, ghzAmp]
  norm_num

example : tangleAB ghzAmp = 0 := by
  norm_num [tangleAB, frobC, detMc, Mc, ghzAmp, Fintype.sum_bool]

example : tangleAC ghzAmp = 0 := by
  norm_num [tangleAC, frobB, detMb, Mb, ghzAmp, Fintype.sum_bool]

example : tangleA wAmp = 8 := by
  simp only [tangleA, detRhoA, Fintype.sum_bool, wAmp]
  norm_num

example : tangleAB wAmp = 4 := by
  norm_num [tangleAB, frobC, detMc, Mc, wAmp, Fintype.sum_bool]

example : tangleAC wAmp = 4 := by
  norm_num [tangleAC, frobB, detMb, Mb, wAmp, Fintype.sum_bool]

end QI

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

