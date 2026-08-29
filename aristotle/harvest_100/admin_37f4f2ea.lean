/-
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
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

set_option grind.warning false

namespace Frontier

open LaurentPolynomial

/-! ## The coefficient ring

The Kauffman bracket takes values in the ring of Laurent polynomials `ℤ[A, A⁻¹]`,
which we realise as `LaurentPolynomial ℤ` with `A = T 1`. -/

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev KR : Type := LaurentPolynomial ℤ

/-- The variable `A`. -/
noncomputable def Avar : KR := T 1

/-- The value `δ = -A² - A⁻²` of a free loop in the Kauffman bracket. -/
noncomputable def loopValue : KR := -T 2 - T (-2)

lemma T_mul_T (a b : ℤ) : (T a : KR) * T b = T (a + b) := (T_add a b).symm

/-- Resolving a positive kink multiplies the bracket by `-A³`. -/
lemma kinkA : (T 1 : KR) * loopValue + T (-1) = -T 3 := by
  simp only [loopValue, mul_sub, mul_neg, T_mul_T]
  norm_num

/-- Resolving a negative kink multiplies the bracket by `-A⁻³`. -/
lemma kinkB : (T (-1) : KR) * loopValue + T 1 = -T (-3) := by
  simp only [loopValue, mul_sub, mul_neg, T_mul_T]
  norm_num
  ring

/-- The Reidemeister II cancellation `A² + A⁻² + δ = 0`. -/
lemma R2_cancel : (T 2 : KR) + T (-2) + loopValue = 0 := by
  simp [loopValue]

/-! ## Axiomatics of the Kauffman bracket

A `KauffmanSystem` packages a type of link diagrams together with the Kauffman
bracket and the writhe, subject to the two defining local relations:

* the *skein relation*: at any crossing, the bracket is `A` times the bracket of the
  `A`-smoothing plus `A⁻¹` times the bracket of the `B`-smoothing (with the roles
  of the two smoothings exchanged when the crossing is switched);
* the *loop relation*: a split disjoint circle multiplies the bracket by `δ`.

A *site* is a diagram with one distinguished crossing left unfilled; `pos`/`neg`
fill it with the two crossings and `sA`/`sB` with the two smoothings.  Nothing
else about diagrams is assumed; the Reidemeister moves are described below by
the planar identifications they induce between such fillings. -/

/-- A system of link diagrams carrying a Kauffman bracket and a writhe. -/
structure KauffmanSystem where
  /-- The type of link diagrams. -/
  D : Type
  /-- The type of diagrams with one distinguished unfilled crossing. -/
  Site : Type
  /-- The Kauffman bracket. -/
  br : D → KR
  /-- The writhe of a diagram. -/
  wr : D → ℤ
  /-- Adding a split disjoint circle to a diagram. -/
  addCircle : D → D
  /-- Fill the distinguished crossing with a positive crossing. -/
  pos : Site → D
  /-- Fill the distinguished crossing with a negative crossing. -/
  neg : Site → D
  /-- Fill the distinguished crossing with the `A`-smoothing of the positive crossing. -/
  sA : Site → D
  /-- Fill the distinguished crossing with the `B`-smoothing of the positive crossing. -/
  sB : Site → D
  /-- Loop relation for the bracket. -/
  br_addCircle : ∀ d, br (addCircle d) = loopValue * br d
  /-- A split circle does not change the writhe. -/
  wr_addCircle : ∀ d, wr (addCircle d) = wr d
  /-- Skein relation at a positive crossing. -/
  br_pos : ∀ s, br (pos s) = T 1 * br (sA s) + T (-1) * br (sB s)
  /-- Skein relation at a negative crossing. -/
  br_neg : ∀ s, br (neg s) = T (-1) * br (sA s) + T 1 * br (sB s)

variable (S : KauffmanSystem)

/-- Data witnessing a Reidemeister I move: a site whose crossing is a kink on the
diagram `base`.  Smoothing the kink one way splits off a circle, the other way
undoes the kink; adding the kink changes the writhe by `±1`. -/
structure R1Move where
  /-- The kink site. -/
  site : S.Site
  /-- The diagram with the kink removed. -/
  base : S.D
  /-- The `A`-smoothing of the kink splits off a circle. -/
  hA : S.sA site = S.addCircle base
  /-- The `B`-smoothing of the kink undoes it. -/
  hB : S.sB site = base
  /-- A positive kink increases the writhe by one. -/
  wr_pos : S.wr (S.pos site) = S.wr base + 1
  /-- A negative kink decreases the writhe by one. -/
  wr_neg : S.wr (S.neg site) = S.wr base - 1

/-- Data witnessing a Reidemeister II move.  The diagram `S.pos top` has two
crossings, an upper positive one (`top`) and a lower negative one; resolving the
upper crossing leaves the diagrams `S.neg botA`, `S.neg botB`, and resolving the
lower crossings produces the two planar tangle fillings `base` (two parallel
strands) and `cap` (a cup on top of a cap), the last state carrying an extra
split circle. -/
structure R2Move where
  /-- The upper (positive) crossing. -/
  top : S.Site
  /-- The lower crossing seen after the `A`-smoothing of `top`. -/
  botA : S.Site
  /-- The lower crossing seen after the `B`-smoothing of `top`. -/
  botB : S.Site
  /-- The filling by two parallel strands: the diagram after the move. -/
  base : S.D
  /-- The filling by a cup on top of a cap. -/
  cap : S.D
  /-- Smoothing the upper crossing one way. -/
  h_top_A : S.sA top = S.neg botA
  /-- Smoothing the upper crossing the other way. -/
  h_top_B : S.sB top = S.neg botB
  /-- Both strands smoothed vertically. -/
  h_botA_A : S.sA botA = base
  /-- Upper vertical, lower horizontal. -/
  h_botA_B : S.sB botA = cap
  /-- Upper horizontal, lower vertical. -/
  h_botB_A : S.sA botB = cap
  /-- Both strands smoothed horizontally: a circle splits off. -/
  h_botB_B : S.sB botB = S.addCircle cap
  /-- The move does not change the writhe. -/
  wr_eq : S.wr (S.pos top) = S.wr base

/-- Data witnessing a Reidemeister III move.  On both sides of the move we
distinguish the crossing that is slid across; one smoothing of it gives planar
isotopic diagrams on the two sides, and the other smoothing gives diagrams which
are related by a Reidemeister II move to planar isotopic diagrams. -/
structure R3Move where
  /-- The distinguished crossing of the left-hand diagram. -/
  left : S.Site
  /-- The distinguished crossing of the right-hand diagram. -/
  right : S.Site
  /-- The two `A`-smoothings agree (planar isotopy). -/
  hA : S.sA left = S.sA right
  /-- The Reidemeister II move simplifying the `B`-smoothing on the left. -/
  r2left : R2Move S
  /-- The Reidemeister II move simplifying the `B`-smoothing on the right. -/
  r2right : R2Move S
  /-- The left `B`-smoothing carries a Reidemeister II pair. -/
  hleft : S.pos r2left.top = S.sB left
  /-- The right `B`-smoothing carries a Reidemeister II pair. -/
  hright : S.pos r2right.top = S.sB right
  /-- After the Reidemeister II reductions the two sides agree (planar isotopy). -/
  hbase : r2left.base = r2right.base
  /-- The move does not change the writhe. -/
  wr_eq : S.wr (S.pos left) = S.wr (S.pos right)

/-! ## Behaviour of the Kauffman bracket under the Reidemeister moves -/

/-- Kauffman bracket under a positive Reidemeister I move: `⟨D⟩ ↦ -A³⟨D⟩`. -/
theorem bracket_R1_pos (m : R1Move S) :
    S.br (S.pos m.site) = -T 3 * S.br m.base := by
  rw [S.br_pos, m.hA, m.hB, S.br_addCircle, ← mul_assoc, ← add_mul, kinkA]

/-- Kauffman bracket under a negative Reidemeister I move: `⟨D⟩ ↦ -A⁻³⟨D⟩`. -/
theorem bracket_R1_neg (m : R1Move S) :
    S.br (S.neg m.site) = -T (-3) * S.br m.base := by
  rw [S.br_neg, m.hA, m.hB, S.br_addCircle, ← mul_assoc, ← add_mul, kinkB]

/-- The Kauffman bracket is invariant under Reidemeister II moves. -/
theorem bracket_R2 (m : R2Move S) : S.br (S.pos m.top) = S.br m.base := by
  rw [S.br_pos, m.h_top_A, m.h_top_B, S.br_neg, S.br_neg, m.h_botA_A, m.h_botA_B,
    m.h_botB_A, m.h_botB_B, S.br_addCircle]
  have h1 : (T 1 : KR) * T (-1) = 1 := by rw [T_mul_T]; norm_num
  have h2 : (T 1 : KR) * T 1 = T 2 := by rw [T_mul_T]; norm_num
  have h3 : (T (-1) : KR) * T (-1) = T (-2) := by rw [T_mul_T]; norm_num
  have hkey : (T 2 : KR) + T (-2) + loopValue = 0 := R2_cancel
  have : (T 1 : KR) * (T (-1) * S.br m.base + T 1 * S.br m.cap) +
      T (-1) * (T (-1) * S.br m.cap + T 1 * (loopValue * S.br m.cap))
      = (T 1 * T (-1)) * S.br m.base
        + ((T 1 * T 1) + (T (-1) * T (-1)) + (T (-1) * T 1) * loopValue) * S.br m.cap := by
    ring
  have h4 : (T (-1) : KR) * T 1 = 1 := by rw [T_mul_T]; norm_num
  rw [this, h1, h2, h3, h4, one_mul, one_mul, hkey, zero_mul, add_zero]

/-- The Kauffman bracket is invariant under Reidemeister III moves. -/
theorem bracket_R3 (m : R3Move S) : S.br (S.pos m.left) = S.br (S.pos m.right) := by
  have hl : S.br (S.sB m.left) = S.br m.r2left.base := by
    rw [← m.hleft, bracket_R2]
  have hr : S.br (S.sB m.right) = S.br m.r2right.base := by
    rw [← m.hright, bracket_R2]
  rw [S.br_pos, S.br_pos, m.hA, hl, hr, m.hbase]

/-! ## The Jones polynomial

The bracket is normalised by the writhe: `f(D) = (-A³)^{-w(D)} ⟨D⟩`.  Since `-A³`
is a unit of `ℤ[A, A⁻¹]` (with inverse `-A⁻³`) the negative powers make sense. -/

/-- The unit `-A³` of `ℤ[A, A⁻¹]`. -/
noncomputable def kinkUnit : KRˣ where
  val := -T 3
  inv := -T (-3)
  val_inv := by rw [neg_mul_neg, T_mul_T]; norm_num
  inv_val := by rw [neg_mul_neg, T_mul_T]; norm_num

@[simp] lemma kinkUnit_val : (kinkUnit : KR) = -T 3 := rfl

@[simp] lemma kinkUnit_inv_val : ((kinkUnit⁻¹ : KRˣ) : KR) = -T (-3) := rfl

/-- The (unnormalised-variable) Jones polynomial of a diagram:
`f(D) = (-A³)^{-w(D)} ⟨D⟩`. -/
noncomputable def jones (d : S.D) : KR :=
  ((kinkUnit ^ (-(S.wr d)) : KRˣ) : KR) * S.br d

lemma jones_def (d : S.D) :
    jones S d = ((kinkUnit ^ (-(S.wr d)) : KRˣ) : KR) * S.br d := rfl

lemma kinkUnit_zpow_succ (n : ℤ) :
    ((kinkUnit ^ (n + 1) : KRˣ) : KR) = ((kinkUnit ^ n : KRˣ) : KR) * (-T 3) := by
  rw [zpow_add_one]
  simp

lemma kinkUnit_zpow_pred (n : ℤ) :
    ((kinkUnit ^ (n - 1) : KRˣ) : KR) = ((kinkUnit ^ n : KRˣ) : KR) * (-T (-3)) := by
  rw [zpow_sub_one]
  simp

/-- Invariance of the Jones polynomial under the positive Reidemeister I move. -/
theorem jones_R1_pos (m : R1Move S) : jones S (S.pos m.site) = jones S m.base := by
  have hw : -(S.wr (S.pos m.site)) = -(S.wr m.base) - 1 := by rw [m.wr_pos]; ring
  have h : (-T (-3) : KR) * (-T 3) = 1 := by rw [neg_mul_neg, T_mul_T]; norm_num
  rw [jones_def, jones_def, bracket_R1_pos, hw, kinkUnit_zpow_pred]
  calc ((kinkUnit ^ (-(S.wr m.base)) : KRˣ) : KR) * (-T (-3)) * (-T 3 * S.br m.base)
      = ((kinkUnit ^ (-(S.wr m.base)) : KRˣ) : KR) * ((-T (-3) : KR) * (-T 3)) * S.br m.base := by
        ring
    _ = ((kinkUnit ^ (-(S.wr m.base)) : KRˣ) : KR) * S.br m.base := by rw [h, mul_one]

/-- Invariance of the Jones polynomial under the negative Reidemeister I move. -/
theorem jones_R1_neg (m : R1Move S) : jones S (S.neg m.site) = jones S m.base := by
  have hw : -(S.wr (S.neg m.site)) = -(S.wr m.base) + 1 := by rw [m.wr_neg]; ring
  have h : (-T 3 : KR) * (-T (-3)) = 1 := by rw [neg_mul_neg, T_mul_T]; norm_num
  rw [jones_def, jones_def, bracket_R1_neg, hw, kinkUnit_zpow_succ]
  calc ((kinkUnit ^ (-(S.wr m.base)) : KRˣ) : KR) * (-T 3) * (-T (-3) * S.br m.base)
      = ((kinkUnit ^ (-(S.wr m.base)) : KRˣ) : KR) * ((-T 3 : KR) * (-T (-3))) * S.br m.base := by
        ring
    _ = ((kinkUnit ^ (-(S.wr m.base)) : KRˣ) : KR) * S.br m.base := by rw [h, mul_one]

/-- Invariance of the Jones polynomial under Reidemeister II moves. -/
theorem jones_R2 (m : R2Move S) : jones S (S.pos m.top) = jones S m.base := by
  rw [jones_def, jones_def, bracket_R2, m.wr_eq]

/-- Invariance of the Jones polynomial under Reidemeister III moves. -/
theorem jones_R3 (m : R3Move S) : jones S (S.pos m.left) = jones S (S.pos m.right) := by
  rw [jones_def, jones_def, bracket_R3, m.wr_eq]

/-- **The Jones polynomial is a link invariant.**  In any system of link diagrams
carrying a Kauffman bracket, the writhe-normalised bracket
`f(D) = (-A³)^{-w(D)} ⟨D⟩` is unchanged by all three Reidemeister moves. -/
theorem jones_polynomial_invariant (S : KauffmanSystem) :
    (∀ m : R1Move S, jones S (S.pos m.site) = jones S m.base ∧
        jones S (S.neg m.site) = jones S m.base) ∧
    (∀ m : R2Move S, jones S (S.pos m.top) = jones S m.base) ∧
    (∀ m : R3Move S, jones S (S.pos m.left) = jones S (S.pos m.right)) :=
  ⟨fun m => ⟨jones_R1_pos S m, jones_R1_neg S m⟩, fun m => jones_R2 S m, fun m => jones_R3 S m⟩

/-! ## A concrete nontrivial model

To see that the axioms above are not vacuous we exhibit a concrete system: the
diagrams `(k, w)` consisting of a round circle with `w` signed kinks together with
`k` split disjoint circles.  Its bracket is `δ^k (-A³)^w`, every crossing site is a
kink site, and the Jones polynomial `δ^k` indeed does not see the kinks. -/

/-- The system of kinked unknot diagrams with split circles. -/
noncomputable def twistSystem : KauffmanSystem where
  D := ℕ × ℤ
  Site := ℕ × ℤ
  br := fun p => loopValue ^ p.1 * ((kinkUnit ^ p.2 : KRˣ) : KR)
  wr := fun p => p.2
  addCircle := fun p => (p.1 + 1, p.2)
  pos := fun p => (p.1, p.2 + 1)
  neg := fun p => (p.1, p.2 - 1)
  sA := fun p => (p.1 + 1, p.2)
  sB := fun p => p
  br_addCircle := by
    rintro ⟨k, w⟩
    simp only [pow_succ]
    ring
  wr_addCircle := by rintro ⟨k, w⟩; rfl
  br_pos := by
    rintro ⟨k, w⟩
    simp only [kinkUnit_zpow_succ, pow_succ]
    linear_combination (-(loopValue ^ k * ((kinkUnit ^ w : KRˣ) : KR))) * kinkA
  br_neg := by
    rintro ⟨k, w⟩
    simp only [kinkUnit_zpow_pred, pow_succ]
    linear_combination (-(loopValue ^ k * ((kinkUnit ^ w : KRˣ) : KR))) * kinkB

/-- Every crossing of the model is a Reidemeister I kink. -/
def twistR1 (k : ℕ) (w : ℤ) : R1Move twistSystem where
  site := (k, w)
  base := (k, w)
  hA := rfl
  hB := rfl
  wr_pos := rfl
  wr_neg := rfl

/-- In the model the bracket is not identically zero: the round circle has
bracket `1`. -/
lemma twistSystem_br_unknot : twistSystem.br (0, 0) = 1 := by
  simp [twistSystem]

/-- The Kauffman bracket of the model is nontrivial, so the axioms of a
`KauffmanSystem` are consistent and the invariance theorem is not vacuous. -/
theorem twistSystem_br_ne_zero : twistSystem.br ≠ 0 := by
  intro h
  have h0 : twistSystem.br (0, 0) = 0 := by rw [h]; rfl
  rw [twistSystem_br_unknot] at h0
  exact one_ne_zero h0

/-- In the model the Jones polynomial of a kinked circle with `k` split circles is
`δ^k`, independently of the number `w` of kinks. -/
theorem jones_twistSystem (k : ℕ) (w : ℤ) : jones twistSystem (k, w) = loopValue ^ k := by
  have h : ((kinkUnit ^ (-w) : KRˣ) : KR) * ((kinkUnit ^ w : KRˣ) : KR) = 1 := by
    rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
  show ((kinkUnit ^ (-w) : KRˣ) : KR) * (loopValue ^ k * ((kinkUnit ^ w : KRˣ) : KR)) = _
  calc ((kinkUnit ^ (-w) : KRˣ) : KR) * (loopValue ^ k * ((kinkUnit ^ w : KRˣ) : KR))
      = (((kinkUnit ^ (-w) : KRˣ) : KR) * ((kinkUnit ^ w : KRˣ) : KR)) * loopValue ^ k := by
        ring
    _ = loopValue ^ k := by rw [h, one_mul]

/-! ## A second model: the Temperley–Lieb algebra on two strands

The model above has only Reidemeister I sites.  A model containing Reidemeister II
and III configurations is provided by the Temperley–Lieb algebra `TL₂` with its
Markov trace: a diagram is an element `a·1 + b·e` of `TL₂`, the bracket is the
trace of its closure, and a crossing site is a pair (prefix, suffix) of `TL₂`
elements between which a crossing or one of its two smoothings is inserted. -/

/-- The Temperley–Lieb algebra on two strands, in the basis `1, e`. -/
abbrev TL2 : Type := KR × KR

/-- Multiplication of `TL₂`, using `e * e = δ * e`. -/
noncomputable def tlMul (x y : TL2) : TL2 :=
  (x.1 * y.1, x.1 * y.2 + x.2 * y.1 + loopValue * (x.2 * y.2))

/-- The cup-cap generator `e` of `TL₂`. -/
noncomputable def tlE : TL2 := (0, 1)

/-- The bracket of the closure of a `TL₂` element (its Markov trace). -/
noncomputable def tlTr (x : TL2) : KR := x.1 * loopValue + x.2

/-- The positive crossing `A·1 + A⁻¹·e`. -/
noncomputable def tlXp : TL2 := (T 1, T (-1))

/-- The negative crossing `A⁻¹·1 + A·e`. -/
noncomputable def tlXn : TL2 := (T (-1), T 1)

lemma tlMul_assoc (x y z : TL2) : tlMul (tlMul x y) z = tlMul x (tlMul y z) := by
  cases x; cases y; cases z
  simp only [tlMul, Prod.mk.injEq]
  constructor <;> ring

lemma tlOne_mul (y : TL2) : tlMul ((1 : KR), (0 : KR)) y = y := by
  cases y
  simp [tlMul]

/-- In `TL₂` the two crossings are inverse to each other. -/
lemma tlXp_mul_tlXn : tlMul tlXp tlXn = ((1 : KR), (0 : KR)) := by
  have h1 : (T 1 : KR) * T (-1) = 1 := by rw [T_mul_T]; norm_num
  have h2 : (T 1 : KR) * T 1 = T 2 := by rw [T_mul_T]; norm_num
  have h3 : (T (-1) : KR) * T (-1) = T (-2) := by rw [T_mul_T]; norm_num
  have h4 : (T (-1) : KR) * T 1 = 1 := by rw [T_mul_T]; norm_num
  have hkey : (T 2 : KR) + T (-2) + loopValue = 0 := R2_cancel
  simp only [tlMul, tlXp, tlXn, Prod.mk.injEq]
  refine ⟨h1, ?_⟩
  rw [h2, h3, h4, mul_one]
  exact hkey

/-- The Reidemeister II identity in `TL₂`: the two crossings cancel. -/
lemma tlMul_Xp_Xn (x y : TL2) : tlMul (tlMul x tlXp) (tlMul tlXn y) = tlMul x y := by
  rw [tlMul_assoc, ← tlMul_assoc tlXp tlXn y, tlXp_mul_tlXn, tlOne_mul]

/-- The Temperley–Lieb model of a Kauffman system. -/
noncomputable def tlSystem : KauffmanSystem where
  D := TL2
  Site := TL2 × TL2
  br := tlTr
  wr := fun _ => 0
  addCircle := fun x => (loopValue * x.1, loopValue * x.2)
  pos := fun s => tlMul (tlMul s.1 tlXp) s.2
  neg := fun s => tlMul (tlMul s.1 tlXn) s.2
  sA := fun s => tlMul s.1 s.2
  sB := fun s => tlMul (tlMul s.1 tlE) s.2
  br_addCircle := by rintro ⟨a, b⟩; simp only [tlTr]; ring
  wr_addCircle := by rintro ⟨a, b⟩; rfl
  br_pos := by
    rintro ⟨⟨p1, p2⟩, ⟨s1, s2⟩⟩
    simp only [tlMul, tlTr, tlXp, tlE]
    ring
  br_neg := by
    rintro ⟨⟨p1, p2⟩, ⟨s1, s2⟩⟩
    simp only [tlMul, tlTr, tlXn, tlE]
    ring

/-- Every pair of `TL₂` elements gives a Reidemeister II configuration in the
Temperley–Lieb model. -/
noncomputable def tlR2 (p s : TL2) : R2Move tlSystem where
  top := (p, tlMul tlXn s)
  botA := (p, s)
  botB := (tlMul p tlE, s)
  base := tlMul p s
  cap := tlMul (tlMul p tlE) s
  h_top_A := (tlMul_assoc p tlXn s).symm
  h_top_B := (tlMul_assoc (tlMul p tlE) tlXn s).symm
  h_botA_A := rfl
  h_botA_B := rfl
  h_botB_A := rfl
  h_botB_B := by
    cases p; cases s
    simp only [tlSystem, tlMul, tlE, Prod.mk.injEq]
    constructor <;> ring
  wr_eq := rfl

/-- The Temperley–Lieb model also contains Reidemeister III configurations. -/
noncomputable def tlR3 (p s : TL2) : R3Move tlSystem where
  left := (p, s)
  right := (p, s)
  hA := rfl
  r2left := tlR2 (tlMul p tlE) s
  r2right := tlR2 (tlMul p tlE) s
  hleft := tlMul_Xp_Xn (tlMul p tlE) s
  hright := tlMul_Xp_Xn (tlMul p tlE) s
  hbase := rfl
  wr_eq := rfl

/-- The bracket of the Temperley–Lieb model is nontrivial. -/
theorem tlSystem_br_ne_zero : tlSystem.br ≠ 0 := by
  intro h
  have h0 : tlSystem.br tlE = 0 := by rw [h]; rfl
  have h1 : tlSystem.br tlE = 1 := by simp [tlSystem, tlTr, tlE]
  rw [h1] at h0
  exact one_ne_zero h0

/-- The hypotheses of `Frontier.jones_polynomial_invariant` are consistent and not
vacuous: there are Kauffman systems with a nonzero bracket containing
Reidemeister I configurations, and Kauffman systems with a nonzero bracket
containing Reidemeister II and III configurations. -/
theorem kauffman_axioms_nonvacuous :
    (∃ S : KauffmanSystem, S.br ≠ 0 ∧ Nonempty (R1Move S)) ∧
    (∃ S : KauffmanSystem, S.br ≠ 0 ∧ Nonempty (R2Move S) ∧ Nonempty (R3Move S)) :=
  ⟨⟨twistSystem, twistSystem_br_ne_zero, ⟨twistR1 0 0⟩⟩,
   ⟨tlSystem, tlSystem_br_ne_zero, ⟨tlR2 ((1 : KR), (0 : KR)) ((1 : KR), (0 : KR))⟩,
     ⟨tlR3 ((1 : KR), (0 : KR)) ((1 : KR), (0 : KR))⟩⟩⟩

end Frontier

