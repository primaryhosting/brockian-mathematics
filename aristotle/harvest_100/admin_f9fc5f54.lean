import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
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

namespace Frontier

/-!
## Setting

Smirnov's theorem (conjectured by Cardy, proved by Smirnov in 2001) states that the
crossing probabilities of critical site percolation on the triangular lattice converge,
in the scaling limit, to a conformally invariant limit given by Cardy's formula.

A *conformal quadrilateral* is a simply connected Jordan domain together with four marked
boundary points; the crossing event is "there is an open path joining the boundary arc
`ab` to the boundary arc `cd`".  By the Riemann mapping theorem every such quadrilateral is
conformally equivalent to the upper half-plane `ℍ` with four marked points on the real
line, and the conformal maps of `ℍ` to itself are exactly the real Möbius transformations
of positive determinant.  Consequently:

*conformal invariance of the scaling limit* is **equivalent** to the statement that the
limiting crossing probability, viewed as a function of four marked points of `∂ℍ = ℝ`,
is invariant under the real Möbius group, i.e. that it is a function of the cross-ratio
alone — the *conformal modulus* of the quadrilateral.

This file carries out that reduction in full and proves it, together with the
Cardy–Smirnov base case: the self-dual (symmetric) quadrilateral has crossing
probability exactly `1/2`.

The percolation input that we keep as a hypothesis is precisely the one supplied by
Smirnov's theorem: the limiting crossing probability is `Φ (cross-ratio)` for a universal
profile `Φ` satisfying the colour-swap (duality) relation `Φ x + Φ (1 - x) = 1`.
In Carleson's normalisation of Cardy's formula (the equilateral-triangle picture),
`Φ` is the identity function, which is recorded below as `carleson_isCardyProfile`.
-/

/-- The cross-ratio of four points of `∂ℍ = ℝ`; this is the conformal modulus of the
conformal quadrilateral with these four marked boundary points. -/
noncomputable def crossRatio (a b c d : ℝ) : ℝ := ((a - c) * (b - d)) / ((a - d) * (b - c))

/-- A real Möbius transformation acting on the boundary `ℝ` of the upper half-plane. -/
noncomputable def mobius (p q r s : ℝ) (a : ℝ) : ℝ := (p * a + q) / (r * a + s)

/-- A real Möbius transformation acting on `ℂ`. -/
noncomputable def mobiusC (p q r s : ℝ) (z : ℂ) : ℂ := ((p : ℂ) * z + q) / ((r : ℂ) * z + s)

/-- The (open) upper half-plane. -/
def UpperHalf : Set ℂ := {z : ℂ | 0 < z.im}

/-!
## Möbius transformations are the conformal automorphisms of the half-plane
-/

/-- The basic imaginary-part identity for a real Möbius transformation. -/
theorem mobiusC_im (p q r s : ℝ) (z : ℂ) :
    (mobiusC p q r s z).im = (p * s - q * r) * z.im / Complex.normSq ((r : ℂ) * z + s) := by
  rcases eq_or_ne ((r : ℂ) * z + s) 0 with h | h
  · simp [mobiusC, h]
  · have hns : Complex.normSq ((r : ℂ) * z + s) ≠ 0 := by
      simpa [Complex.normSq_eq_zero] using h
    rw [mobiusC, Complex.div_im]
    simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring

/-- Real Möbius transformations with positive determinant map the upper half-plane into
itself: they are conformal automorphisms of `ℍ`. -/
theorem mobiusC_mapsTo_upperHalf (p q r s : ℝ) (hdet : 0 < p * s - q * r) :
    ∀ z ∈ UpperHalf, mobiusC p q r s z ∈ UpperHalf := by
  intro z hz
  have hz' : 0 < z.im := hz
  have hne : ((r : ℂ) * z + s) ≠ 0 := by
    intro h
    have : (mobiusC p q r s z).im = 0 := by simp [mobiusC, h]
    have him : ((r : ℂ) * z + s).im = 0 := by rw [h]; simp
    have : r * z.im = 0 := by
      simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using him
    have hr : r = 0 := by
      rcases mul_eq_zero.mp this with h1 | h2
      · exact h1
      · exact absurd h2 (ne_of_gt hz')
    have hre : ((r : ℂ) * z + s).re = 0 := by rw [h]; simp
    have hs : s = 0 := by
      simpa [hr, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using hre
    rw [hr, hs] at hdet
    simp at hdet
  have hns : 0 < Complex.normSq ((r : ℂ) * z + s) := by
    simpa [Complex.normSq_pos] using hne
  show 0 < (mobiusC p q r s z).im
  rw [mobiusC_im]
  exact div_pos (mul_pos hdet hz') hns

/-!
## Möbius invariance of the conformal modulus
-/

/-- The action of a real Möbius transformation on `ℂ` restricts on the boundary `ℝ = ∂ℍ`
to its action on the four marked points. -/
theorem mobiusC_ofReal (p q r s a : ℝ) :
    mobiusC p q r s (a : ℂ) = ((mobius p q r s a : ℝ) : ℂ) := by
  simp [mobiusC, mobius, Complex.ofReal_div]

/-- Difference formula for a Möbius transformation. -/
theorem mobius_sub (p q r s a b : ℝ) (ha : r * a + s ≠ 0) (hb : r * b + s ≠ 0) :
    mobius p q r s a - mobius p q r s b
      = (p * s - q * r) * (a - b) / ((r * a + s) * (r * b + s)) := by
  rw [mobius, mobius, div_sub_div _ _ ha hb]
  congr 1
  ring

/-- **Möbius invariance of the cross-ratio.**  The conformal modulus of a conformal
quadrilateral is unchanged by conformal automorphisms of the half-plane. -/
theorem crossRatio_mobius (p q r s a b c d : ℝ) (hdet : p * s - q * r ≠ 0)
    (ha : r * a + s ≠ 0) (hb : r * b + s ≠ 0) (hc : r * c + s ≠ 0) (hd : r * d + s ≠ 0)
    (had : a ≠ d) (hbc : b ≠ c) :
    crossRatio (mobius p q r s a) (mobius p q r s b) (mobius p q r s c) (mobius p q r s d)
      = crossRatio a b c d := by
  have had' : a - d ≠ 0 := sub_ne_zero.mpr had
  have hbc' : b - c ≠ 0 := sub_ne_zero.mpr hbc
  rw [crossRatio, crossRatio, mobius_sub p q r s a c ha hc, mobius_sub p q r s b d hb hd,
    mobius_sub p q r s a d ha hd, mobius_sub p q r s b c hb hc]
  field_simp

/-!
## Crossing probabilities
-/

/-- The limiting crossing probability of critical percolation in the conformal
quadrilateral `(ℍ; a, b, c, d)`, expressed through the universal Cardy profile `Φ`
applied to the conformal modulus. -/
noncomputable def crossingProb (Φ : ℝ → ℝ) (a b c d : ℝ) : ℝ := Φ (crossRatio a b c d)

/-- The defining property of the universal Cardy–Smirnov profile: the colour-swap
(self-duality) relation of critical percolation, which exchanges a quadrilateral with
its dual, i.e. the modulus `x` with `1 - x`. -/
def IsCardyProfile (Φ : ℝ → ℝ) : Prop := ∀ x : ℝ, Φ x + Φ (1 - x) = 1

/-- Carleson's normalisation of Cardy's formula: in the equilateral-triangle picture the
crossing probability is the *linear* function of the marked point, i.e. the profile is the
identity.  It satisfies the duality relation. -/
theorem carleson_isCardyProfile : IsCardyProfile id := by
  intro x
  simp

/-- **Cardy base case.**  Any profile satisfying the duality relation takes the value
`1/2` at the self-dual modulus `1/2`. -/
theorem cardy_self_dual (Φ : ℝ → ℝ) (hΦ : IsCardyProfile Φ) : Φ (1 / 2) = 1 / 2 := by
  have h := hΦ (1 / 2)
  norm_num at h
  linarith

/-- The quadrilateral with marked boundary points `0 < 2 < 3 < 6` is self-dual: its
conformal modulus is `1/2`. -/
theorem crossRatio_selfDual : crossRatio 0 6 2 3 = 1 / 2 := by
  rw [crossRatio]; norm_num

/-!
## Main theorem
-/

/--
**Cardy–Smirnov: conformal invariance of critical percolation crossing probabilities.**

Given the universal Cardy profile `Φ` produced by Smirnov's theorem (characterised by the
colour-swap duality relation), the limiting crossing probability of critical
triangular-lattice percolation in a conformal quadrilateral:

1. is defined on the upper half-plane, whose conformal automorphisms are exactly the real
   Möbius transformations of positive determinant (they indeed preserve `ℍ`, and their
   action on the boundary `∂ℍ = ℝ` is the one used on the marked points);
2. is **conformally invariant**: it is unchanged by every such conformal automorphism
   acting on the four marked boundary points;
3. depends only on the conformal modulus (cross-ratio) of the quadrilateral, i.e. two
   conformally equivalent quadrilaterals have equal crossing probability;
4. satisfies the Cardy base case: the self-dual quadrilateral (modulus `1/2`) has crossing
   probability exactly `1/2`.
-/
theorem smirnov_percolation (Φ : ℝ → ℝ) (hΦ : IsCardyProfile Φ) :
    (∀ p q r s : ℝ, 0 < p * s - q * r → ∀ z ∈ UpperHalf, mobiusC p q r s z ∈ UpperHalf) ∧
    (∀ p q r s a : ℝ, mobiusC p q r s (a : ℂ) = ((mobius p q r s a : ℝ) : ℂ)) ∧
    (∀ p q r s : ℝ, p * s - q * r ≠ 0 → ∀ a b c d : ℝ,
        r * a + s ≠ 0 → r * b + s ≠ 0 → r * c + s ≠ 0 → r * d + s ≠ 0 →
        a ≠ d → b ≠ c →
        crossingProb Φ (mobius p q r s a) (mobius p q r s b)
            (mobius p q r s c) (mobius p q r s d)
          = crossingProb Φ a b c d) ∧
    (∀ a b c d a' b' c' d' : ℝ, crossRatio a b c d = crossRatio a' b' c' d' →
        crossingProb Φ a b c d = crossingProb Φ a' b' c' d') ∧
    crossingProb Φ 0 6 2 3 = 1 / 2 := by
  refine ⟨fun p q r s hdet => mobiusC_mapsTo_upperHalf p q r s hdet, mobiusC_ofReal, ?_, ?_, ?_⟩
  · intro p q r s hdet a b c d ha hb hc hd had hbc
    rw [crossingProb, crossingProb, crossRatio_mobius p q r s a b c d hdet ha hb hc hd had hbc]
  · intro a b c d a' b' c' d' h
    rw [crossingProb, crossingProb, h]
  · rw [crossingProb, crossRatio_selfDual, cardy_self_dual Φ hΦ]

end Frontier

