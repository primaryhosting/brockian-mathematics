import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Overview

We formalise the skein-theoretic heart of Jones' theorem: the normalised Kauffman
bracket

  V(L) = (-A^3)^(-w(L)) * ⟨L⟩

is unchanged by the three Reidemeister moves.

Diagrams are kept abstract: they form an arbitrary type `D` equipped with a
bracket `br : D → ℤ[A, A⁻¹]`, an operation `addCircle` adding a disjoint
unknotted circle, and the circle axiom `⟨D ⊔ ○⟩ = δ ⟨D⟩` with
`δ = -A² - A⁻²`.  The Kauffman skein relation

  ⟨crossing⟩ = A ⟨A-smoothing⟩ + A⁻¹ ⟨B-smoothing⟩

enters as an explicit hypothesis at each crossing that a given Reidemeister
move touches; this is exactly the local data a link diagram provides.  From
these hypotheses we *derive* the classical consequences:

* R1 changes the bracket by the factor `-A^±3` (and hence leaves `V` invariant,
  since the writhe changes by `∓1`);
* R2 leaves the bracket unchanged;
* R3 leaves the bracket unchanged (its `B`-smoothings are compared using the
  R2 computation).

All the polynomial arithmetic takes place in the Laurent polynomial ring
`ℤ[A, A⁻¹] = LaurentPolynomial ℤ`, with `A = T 1`.
-/


namespace Frontier

open LaurentPolynomial

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev KL : Type := LaurentPolynomial ℤ

/-- The Kauffman variable `A`. -/
noncomputable def Avar : KL := T 1

/-- The inverse `A⁻¹` of the Kauffman variable. -/
noncomputable def Ainv : KL := T (-1)

/-- The loop value `δ = -A² - A⁻²`. -/
noncomputable def delta : KL := -T 2 - T (-2)

@[simp] lemma Avar_mul_Ainv : Avar * Ainv = 1 := by
  rw [Avar, Ainv, ← T_add]; norm_num

@[simp] lemma Ainv_mul_Avar : Ainv * Avar = 1 := by
  rw [mul_comm]; exact Avar_mul_Ainv

/-- The defining property of the loop value: `A² + δ + A⁻² = 0`. -/
lemma sq_add_delta_add_invSq : Avar * Avar + delta + Ainv * Ainv = 0 := by
  rw [Avar, Ainv, delta, ← T_add, ← T_add]; norm_num; ring

/-- The positive kink factor: `A δ + A⁻¹ = -A³`. -/
lemma Avar_mul_delta_add_Ainv : Avar * delta + Ainv = -T 3 := by
  rw [Avar, Ainv, delta, mul_sub, mul_neg, ← T_add, ← T_add]; norm_num

/-- The negative kink factor: `A⁻¹ δ + A = -A⁻³`. -/
lemma Ainv_mul_delta_add_Avar : Ainv * delta + Avar = -T (-3) := by
  rw [Avar, Ainv, delta, mul_sub, mul_neg, ← T_add, ← T_add]; norm_num; ring

/-- A Kauffman bracket on an abstract type of link diagrams: a map to
`ℤ[A, A⁻¹]`, together with the operation of adding a disjoint circle and the
axiom `⟨D ⊔ ○⟩ = δ ⟨D⟩`. -/
structure KauffmanBracket (D : Type*) where
  /-- The bracket polynomial of a diagram. -/
  br : D → KL
  /-- Add a disjoint unknotted circle to a diagram. -/
  addCircle : D → D
  /-- Adding a disjoint circle multiplies the bracket by `δ`. -/
  br_addCircle : ∀ d, br (addCircle d) = delta * br d

variable {D : Type*}

/-- Kauffman brackets exist: taking a diagram to be a finite disjoint union of
`n` unknotted circles, with bracket `δ ^ n`, satisfies the circle axiom.  This
shows the hypotheses of the results below are not vacuous. -/
noncomputable def circlesBracket : KauffmanBracket ℕ where
  br n := delta ^ n
  addCircle := Nat.succ
  br_addCircle n := by rw [pow_succ]; ring

/-!
### Reidemeister move I
-/

/-- **R1, positive kink.**  If `dk` is obtained from `strand` by adding a kink
whose `A`-smoothing splits off a circle and whose `B`-smoothing undoes the
kink, then `⟨dk⟩ = -A³ ⟨strand⟩`. -/
theorem bracket_R1_pos (K : KauffmanBracket D) (dk strand : D)
    (h : K.br dk = Avar * K.br (K.addCircle strand) + Ainv * K.br strand) :
    K.br dk = (-T 3 : KL) * K.br strand := by
  rw [h, K.br_addCircle, ← Avar_mul_delta_add_Ainv]
  ring

/-- **R1, negative kink.**  The mirror computation gives the factor `-A⁻³`. -/
theorem bracket_R1_neg (K : KauffmanBracket D) (dk strand : D)
    (h : K.br dk = Avar * K.br strand + Ainv * K.br (K.addCircle strand)) :
    K.br dk = (-T (-3) : KL) * K.br strand := by
  rw [h, K.br_addCircle, ← Ainv_mul_delta_add_Avar]
  ring

/-!
### Reidemeister move II
-/

/-- **R2.**  Resolving the two crossings of an R2 tangle produces, in order,
the `A`-resolution `eA` (which resolves further into the horizontal smoothing
`cupcap` and the trivial tangle `idt`) and the `B`-resolution `eB` (which
resolves into `cupcap` with a free circle, and `cupcap`).  The bracket is then
unchanged by the move. -/
theorem bracket_R2 (K : KauffmanBracket D) (d2 eA eB cupcap idt : D)
    (h1 : K.br d2 = Avar * K.br eA + Ainv * K.br eB)
    (h2 : K.br eA = Avar * K.br cupcap + Ainv * K.br idt)
    (h3 : K.br eB = Avar * K.br (K.addCircle cupcap) + Ainv * K.br cupcap) :
    K.br d2 = K.br idt := by
  rw [h1, h2, h3, K.br_addCircle]
  linear_combination (K.br cupcap) * sq_add_delta_add_invSq
    + (delta * K.br cupcap + K.br idt) * Avar_mul_Ainv

/-!
### Reidemeister move III
-/

/-- **R3.**  Resolve the crossing that moves across the third strand in both
diagrams.  The `A`-resolutions `aL`, `aR` agree by planar isotopy, while the
`B`-resolutions `bL`, `bR` are each simplified by an R2 move to a common
diagram (with resolution data `_L`/`_R`).  Hence the brackets agree. -/
theorem bracket_R3 (K : KauffmanBracket D)
    (dL dR aL aR bL bR eAL eBL eAR eBR cupcapL cupcapR common : D)
    (h1 : K.br dL = Avar * K.br aL + Ainv * K.br bL)
    (h2 : K.br dR = Avar * K.br aR + Ainv * K.br bR)
    (ha : K.br aL = K.br aR)
    (hbL1 : K.br bL = Avar * K.br eAL + Ainv * K.br eBL)
    (hbL2 : K.br eAL = Avar * K.br cupcapL + Ainv * K.br common)
    (hbL3 : K.br eBL = Avar * K.br (K.addCircle cupcapL) + Ainv * K.br cupcapL)
    (hbR1 : K.br bR = Avar * K.br eAR + Ainv * K.br eBR)
    (hbR2 : K.br eAR = Avar * K.br cupcapR + Ainv * K.br common)
    (hbR3 : K.br eBR = Avar * K.br (K.addCircle cupcapR) + Ainv * K.br cupcapR) :
    K.br dL = K.br dR := by
  have hL : K.br bL = K.br common := bracket_R2 K bL eAL eBL cupcapL common hbL1 hbL2 hbL3
  have hR : K.br bR = K.br common := bracket_R2 K bR eAR eBR cupcapR common hbR1 hbR2 hbR3
  rw [h1, h2, ha, hL, hR]

/-!
### The Jones normalisation
-/

/-- The unit `-A³` of `ℤ[A, A⁻¹]`, whose inverse is `-A⁻³`. -/
noncomputable def kinkUnit : KLˣ where
  val := -T 3
  inv := -T (-3)
  val_inv := by rw [neg_mul_neg, ← T_add]; norm_num
  inv_val := by rw [neg_mul_neg, ← T_add]; norm_num

@[simp] lemma kinkUnit_val : (kinkUnit : KL) = -T 3 := rfl

@[simp] lemma kinkUnit_inv_val : ((kinkUnit⁻¹ : KLˣ) : KL) = -T (-3) := rfl

/-- The Jones polynomial of a diagram with writhe `w` and bracket `b`:
`V = (-A³)^(-w) ⟨L⟩`. -/
noncomputable def jones (w : ℤ) (b : KL) : KL := ((kinkUnit⁻¹ ^ w : KLˣ) : KL) * b

lemma jones_zero (b : KL) : jones 0 b = b := by simp [jones]

/-- Multiplying the bracket by `-A³` while increasing the writhe by one leaves
the Jones polynomial unchanged. -/
lemma jones_succ_kink (w : ℤ) (b : KL) :
    jones (w + 1) ((-T 3 : KL) * b) = jones w b := by
  have : ((-T 3 : KL)) = ((kinkUnit : KLˣ) : KL) := rfl
  rw [jones, jones, this, zpow_add_one, ← mul_assoc]
  norm_cast
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-- Multiplying the bracket by `-A⁻³` while decreasing the writhe by one leaves
the Jones polynomial unchanged. -/
lemma jones_pred_kink (w : ℤ) (b : KL) :
    jones (w - 1) ((-T (-3) : KL) * b) = jones w b := by
  have : ((-T (-3) : KL)) = ((kinkUnit⁻¹ : KLˣ) : KL) := rfl
  rw [jones, jones, this, zpow_sub_one, ← mul_assoc]
  norm_cast
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-!
### Main theorem
-/

/-- **The Jones polynomial is a link invariant.**

For any Kauffman bracket on an abstract type of link diagrams, the normalised
bracket `V(L) = (-A³)^{-w(L)} ⟨L⟩` is invariant under all three Reidemeister
moves:

1. a positive kink (R1) multiplies the bracket by `-A³` and the writhe by `+1`,
   and the two changes cancel;
2. a negative kink (R1) multiplies the bracket by `-A⁻³` and the writhe by `-1`,
   and again the changes cancel;
3. an R2 move leaves both the bracket and the writhe unchanged;
4. an R3 move leaves both the bracket and the writhe unchanged.

In each clause the hypotheses are the instances of the Kauffman skein relation
`⟨crossing⟩ = A ⟨A-smoothing⟩ + A⁻¹ ⟨B-smoothing⟩` at the crossings involved in
the move. -/
theorem jones_polynomial_invariant {D : Type*} (K : KauffmanBracket D) :
    -- R1, positive kink
    (∀ (w : ℤ) (dk strand : D),
        K.br dk = Avar * K.br (K.addCircle strand) + Ainv * K.br strand →
        jones (w + 1) (K.br dk) = jones w (K.br strand)) ∧
    -- R1, negative kink
    (∀ (w : ℤ) (dk strand : D),
        K.br dk = Avar * K.br strand + Ainv * K.br (K.addCircle strand) →
        jones (w - 1) (K.br dk) = jones w (K.br strand)) ∧
    -- R2
    (∀ (w : ℤ) (d2 eA eB cupcap idt : D),
        K.br d2 = Avar * K.br eA + Ainv * K.br eB →
        K.br eA = Avar * K.br cupcap + Ainv * K.br idt →
        K.br eB = Avar * K.br (K.addCircle cupcap) + Ainv * K.br cupcap →
        jones w (K.br d2) = jones w (K.br idt)) ∧
    -- R3
    (∀ (w : ℤ) (dL dR aL aR bL bR eAL eBL eAR eBR cupcapL cupcapR common : D),
        K.br dL = Avar * K.br aL + Ainv * K.br bL →
        K.br dR = Avar * K.br aR + Ainv * K.br bR →
        K.br aL = K.br aR →
        K.br bL = Avar * K.br eAL + Ainv * K.br eBL →
        K.br eAL = Avar * K.br cupcapL + Ainv * K.br common →
        K.br eBL = Avar * K.br (K.addCircle cupcapL) + Ainv * K.br cupcapL →
        K.br bR = Avar * K.br eAR + Ainv * K.br eBR →
        K.br eAR = Avar * K.br cupcapR + Ainv * K.br common →
        K.br eBR = Avar * K.br (K.addCircle cupcapR) + Ainv * K.br cupcapR →
        jones w (K.br dL) = jones w (K.br dR)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w dk strand h
    rw [bracket_R1_pos K dk strand h, jones_succ_kink]
  · intro w dk strand h
    rw [bracket_R1_neg K dk strand h, jones_pred_kink]
  · intro w d2 eA eB cupcap idt h1 h2 h3
    rw [bracket_R2 K d2 eA eB cupcap idt h1 h2 h3]
  · intro w dL dR aL aR bL bR eAL eBL eAR eBR cupcapL cupcapR common
      h1 h2 ha hbL1 hbL2 hbL3 hbR1 hbR2 hbR3
    rw [bracket_R3 K dL dR aL aR bL bR eAL eBL eAR eBR cupcapL cupcapR common
      h1 h2 ha hbL1 hbL2 hbL3 hbR1 hbR2 hbR3]

#print axioms Frontier.jones_polynomial_invariant

end Frontier

