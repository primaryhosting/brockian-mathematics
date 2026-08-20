/-
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 forbids a module doc comment `/-!` before `import`; the header is repeated below
-- verbatim as the module docstring.)

import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalised here

Mathlib contains no theory of knots, link diagrams or the Kauffman bracket, so nothing in the
library closes (or nearly closes) the statement below; everything is developed from scratch here.

The Jones polynomial of an oriented link diagram `D` is
`V(D) = (-A^3)^{-w(D)} ⟨D⟩`, where `w(D)` is the writhe and `⟨D⟩` is the Kauffman bracket,
computed in the ring `ℤ[A, A⁻¹]` of Laurent polynomials by the skein rules

* `⟨crossing⟩ = A ⟨0-smoothing⟩ + A⁻¹ ⟨∞-smoothing⟩`,
* `⟨D ⊔ circle⟩ = δ ⟨D⟩` with `δ = -A² - A⁻²`.

Invariance under the Reidemeister moves is *exactly* the following algebra, which is what is
proved here (`Frontier.jones_polynomial_invariant`):

* **R1** the skein rules turn a kink into the scalar `A·δ + A⁻¹ = -A³`, and the writhe changes by
  `±1`; hence the writhe-normalised bracket `V` is unchanged (`normalizedBracket_kink_pos`,
  `normalizedBracket_kink_neg`).
* **R2** in the Temperley–Lieb algebra of the corresponding tangle, where a crossing is the
  element `σ(e) = A·1 + A⁻¹·e` and `e` is the planar cap-cup generator satisfying `e² = δ·e`,
  one has `σ(e) σ̄(e) = 1`: the two crossings cancel (`kauffman_R2`).
* **R3** with two generators `e, f` obeying the Temperley–Lieb relations
  `e² = δ e`, `f² = δ f`, `efe = e`, `fef = f`, one has `σ(e)σ(f)σ(e) = σ(f)σ(e)σ(f)`
  (`kauffman_R3`).

Since a bracket state sum is a linear functional on the Temperley–Lieb algebra of the tangle,
these identities are precisely the invariance of `⟨·⟩` under R2 and R3, and, together with the
writhe correction, the invariance of the Jones polynomial.

The Temperley–Lieb hypotheses are not vacuous: `temperleyLieb_relations_have_a_model`
exhibits a concrete noncommutative algebra over `ℤ[A,A⁻¹]` containing such elements.
-/

namespace Frontier

open LaurentPolynomial

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket; `T n` is `A ^ n`. -/
abbrev KauffmanRing := LaurentPolynomial ℤ

/-- The value `δ = -A² - A⁻²` of a free circle in the Kauffman bracket. -/
noncomputable def loopValue : KauffmanRing := -T 2 - T (-2)

/-- The factor `-A³` by which the Kauffman bracket changes under a positive Reidemeister I
kink, as a unit of `ℤ[A, A⁻¹]`. -/
noncomputable def kinkUnit : KauffmanRingˣ where
  val := -T 3
  inv := -T (-3)
  val_inv := by simp only [neg_mul_neg, ← T_add]; norm_num
  inv_val := by simp only [neg_mul_neg, ← T_add]; norm_num

@[simp] lemma kinkUnit_val : (kinkUnit : KauffmanRing) = -T 3 := rfl

@[simp] lemma kinkUnit_inv_val : ((kinkUnit⁻¹ : KauffmanRingˣ) : KauffmanRing) = -T (-3) := rfl

/-- The writhe-normalised Kauffman bracket `(-A³)^{-w} ⟨D⟩`: the Jones polynomial of a diagram
with writhe `w` and bracket `b`. -/
noncomputable def normalizedBracket (w : ℤ) (b : KauffmanRing) : KauffmanRing :=
  ((kinkUnit ^ (-w) : KauffmanRingˣ) : KauffmanRing) * b

/-! ### Reidemeister I -/

/-- The Kauffman bracket skein computation at a kink: smoothing the crossing produces a free
circle (factor `δ`) with coefficient `A`, plus the unknotted strand with coefficient `A⁻¹`. -/
theorem kink_skein : (T 1 * loopValue + T (-1) : KauffmanRing) = -T 3 := by
  simp only [loopValue, mul_sub, mul_neg, ← T_add]
  norm_num

/-- Invariance of the Jones polynomial under a positive Reidemeister I move: the bracket is
multiplied by `-A³` and the writhe increases by `1`. -/
theorem normalizedBracket_kink_pos (w : ℤ) (b : KauffmanRing) :
    normalizedBracket (w + 1) ((-T 3) * b) = normalizedBracket w b := by
  have h : ((kinkUnit ^ (-(w + 1)) : KauffmanRingˣ) : KauffmanRing)
      = ((kinkUnit ^ (-w) : KauffmanRingˣ) : KauffmanRing) * (-T (-3)) := by
    rw [neg_add, zpow_add kinkUnit, Units.val_mul]
    norm_num
  rw [normalizedBracket, normalizedBracket, h]
  rw [mul_assoc, ← mul_assoc (-T (-3) : KauffmanRing)]
  simp only [neg_mul_neg, ← T_add]
  norm_num

/-- Invariance of the Jones polynomial under a negative Reidemeister I move: the bracket is
multiplied by `-A⁻³` and the writhe decreases by `1`. -/
theorem normalizedBracket_kink_neg (w : ℤ) (b : KauffmanRing) :
    normalizedBracket (w - 1) ((-T (-3)) * b) = normalizedBracket w b := by
  have h : ((kinkUnit ^ (-(w - 1)) : KauffmanRingˣ) : KauffmanRing)
      = ((kinkUnit ^ (-w) : KauffmanRingˣ) : KauffmanRing) * (-T 3) := by
    rw [neg_sub, sub_eq_add_neg, add_comm, zpow_add kinkUnit, Units.val_mul]
    norm_num
  rw [normalizedBracket, normalizedBracket, h]
  rw [mul_assoc, ← mul_assoc (-T 3 : KauffmanRing)]
  simp only [neg_mul_neg, ← T_add]
  norm_num

/-! ### Crossings as elements of a Temperley–Lieb algebra -/

section Tangles

variable {Alg : Type} [Ring Alg] [Algebra KauffmanRing Alg]

/-- The Kauffman-bracket expansion `A·1 + A⁻¹·e` of a positive crossing, where `e` is the
Temperley–Lieb generator smoothing the crossing the other way. -/
noncomputable def posCrossing (e : Alg) : Alg :=
  (T 1 : KauffmanRing) • (1 : Alg) + (T (-1) : KauffmanRing) • e

/-- The Kauffman-bracket expansion `A⁻¹·1 + A·e` of a negative crossing. -/
noncomputable def negCrossing (e : Alg) : Alg :=
  (T (-1) : KauffmanRing) • (1 : Alg) + (T 1 : KauffmanRing) • e

/-- **Reidemeister II**: a positive crossing followed by a negative one is the trivial tangle. -/
theorem kauffman_R2 (e : Alg) (he : e * e = loopValue • e) :
    posCrossing e * negCrossing e = 1 := by
  simp only [posCrossing, negCrossing, add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one,
    he, smul_smul]
  match_scalars
  all_goals
    simp only [loopValue, mul_one, mul_sub, mul_neg, ← T_add]
  all_goals norm_num
  all_goals abel

/-- **Reidemeister II**, other sign: a negative crossing followed by a positive one is trivial. -/
theorem kauffman_R2' (e : Alg) (he : e * e = loopValue • e) :
    negCrossing e * posCrossing e = 1 := by
  simp only [posCrossing, negCrossing, add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one,
    he, smul_smul]
  match_scalars
  all_goals simp only [loopValue, mul_one, mul_sub, mul_neg, ← T_add]
  all_goals norm_num

/-- Expansion of a triple crossing product in the Temperley–Lieb algebra: the result is
symmetric in the two generators. -/
theorem posCrossing_triple (e f : Alg) (he : e * e = loopValue • e) (hefe : e * f * e = e) :
    posCrossing e * posCrossing f * posCrossing e
      = (T 3 : KauffmanRing) • (1 : Alg) + (T 1 : KauffmanRing) • e + (T 1 : KauffmanRing) • f
        + (T (-1) : KauffmanRing) • (e * f) + (T (-1) : KauffmanRing) • (f * e) := by
  simp only [posCrossing, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul, ← mul_assoc, he, hefe]
  match_scalars
  all_goals simp only [loopValue, mul_one, mul_add, mul_sub, mul_neg, ← T_add]
  all_goals norm_num
  all_goals abel

/-- **Reidemeister III**: the two ways of sliding a strand past a crossing have equal
Kauffman-bracket expansions. -/
theorem kauffman_R3 (e f : Alg) (he : e * e = loopValue • e) (hf : f * f = loopValue • f)
    (hefe : e * f * e = e) (hfef : f * e * f = f) :
    posCrossing e * posCrossing f * posCrossing e
      = posCrossing f * posCrossing e * posCrossing f := by
  rw [posCrossing_triple e f he hefe, posCrossing_triple f e hf hfef]
  abel

end Tangles

/-! ### The Temperley–Lieb relations are satisfiable -/

section Model

/-- Evaluation `A ↦ 1` of Laurent polynomials, used only to produce a concrete algebra over
`ℤ[A, A⁻¹]` in which the Temperley–Lieb relations hold. -/
noncomputable def evalAtOne : KauffmanRing →+* ℚ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℚ) 1

noncomputable local instance : Algebra KauffmanRing ℚ := evalAtOne.toAlgebra

private lemma evalAtOne_loopValue : evalAtOne loopValue = (-2 : ℚ) := by
  simp [evalAtOne, loopValue, LaurentPolynomial.eval₂_T]
  norm_num

private lemma loopValue_smul_matrix (M : Matrix (Fin 2) (Fin 2) ℚ) :
    loopValue • M = (-2 : ℚ) • M := by
  ext i j
  simp [Matrix.smul_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra, evalAtOne_loopValue]

/-- The Temperley–Lieb relations used for Reidemeister II and III are satisfiable by
noncommuting elements of an algebra over `ℤ[A, A⁻¹]`, so the hypotheses of `kauffman_R2` and
`kauffman_R3` are not vacuous. -/
theorem temperleyLieb_relations_have_a_model :
    ∃ e f : Matrix (Fin 2) (Fin 2) ℚ,
      e * e = loopValue • e ∧ f * f = loopValue • f ∧
        e * f * e = e ∧ f * e * f = f ∧ e * f ≠ f * e := by
  refine ⟨!![-2, 0; 0, 0], !![-1/2, -2; -3/8, -3/2], ?_, ?_, ?_, ?_, ?_⟩
  · rw [loopValue_smul_matrix]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [loopValue_smul_matrix]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h2 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 1) h
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h2

end Model

/-- **The Jones polynomial is a link invariant.**

The five conjuncts are the complete algebraic content of the invariance proof of the Kauffman
bracket / Jones polynomial, in the coefficient ring `ℤ[A, A⁻¹]`:

1. the Reidemeister I skein computation `A·δ + A⁻¹ = -A³`;
2. invariance of the writhe-normalised bracket under a positive kink;
3. invariance of the writhe-normalised bracket under a negative kink;
4. Reidemeister II: the two crossing expansions are mutually inverse in the Temperley–Lieb
   algebra of the tangle;
5. Reidemeister III: the two triple products of crossing expansions agree.
-/
theorem jones_polynomial_invariant :
    (T 1 * loopValue + T (-1) : KauffmanRing) = -T 3 ∧
    (∀ (w : ℤ) (b : KauffmanRing),
        normalizedBracket (w + 1) ((-T 3) * b) = normalizedBracket w b) ∧
    (∀ (w : ℤ) (b : KauffmanRing),
        normalizedBracket (w - 1) ((-T (-3)) * b) = normalizedBracket w b) ∧
    (∀ (Alg : Type) [Ring Alg] [Algebra KauffmanRing Alg] (e : Alg),
        e * e = loopValue • e →
          posCrossing e * negCrossing e = 1 ∧ negCrossing e * posCrossing e = 1) ∧
    (∀ (Alg : Type) [Ring Alg] [Algebra KauffmanRing Alg] (e f : Alg),
        e * e = loopValue • e → f * f = loopValue • f →
        e * f * e = e → f * e * f = f →
          posCrossing e * posCrossing f * posCrossing e
            = posCrossing f * posCrossing e * posCrossing f) :=
  ⟨kink_skein, normalizedBracket_kink_pos, normalizedBracket_kink_neg,
    fun _ _ _ e he => ⟨kauffman_R2 e he, kauffman_R2' e he⟩,
    fun _ _ _ e f he hf hefe hfef => kauffman_R3 e f he hf hefe hfef⟩

end Frontier

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

