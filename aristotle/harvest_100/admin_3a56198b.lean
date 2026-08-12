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

import Mathlib

/-!
# Reidemeister invariance of the (writhe-normalized) Kauffman bracket

This file formalizes the algebraic core of the statement *"the Jones polynomial is a link
invariant"*, i.e. that the writhe-normalized Kauffman bracket is unchanged by the three
Reidemeister moves.

The set-up is the standard *local skein* axiomatization.  A `KauffmanBracket` consists of

* a coefficient ring `R` together with an invertible element `A : Rˣ`;
* a monoid `T` of *local tangles* (composition = vertical stacking), containing the two
  Temperley–Lieb cap–cup elements `e 0`, `e 1` and the two kinds of crossings
  `xp i`, `xm i` sitting at position `i`;
* a type `D` of link diagrams and a type `Ctx` of *contexts*, i.e. diagrams with a hole in
  which a local tangle can be inserted, via `plug : Ctx → T → D`; contexts can absorb tangles
  on either side (`pre`, `post`);
* a bracket functional `br : D → R`,

subject to Kauffman's axioms: the two skein relations, the loop relation
`⟨D ⊔ ○⟩ = (-A² - A⁻²) ⟨D⟩`, the relation `e i * e i = ○ · e i`, and the Temperley–Lieb
relations `e i * e j * e i = e i`.

From these purely local axioms we prove:

* `KauffmanBracket.br_R2` : invariance of the bracket under the second Reidemeister move;
* `KauffmanBracket.br_R3` : invariance of the bracket under the third Reidemeister move;
* `KauffmanBracket.br_kink_xm` / `br_kink_xp` : a curl multiplies the bracket by `-A³`
  (resp. `-A⁻³`), whence the *writhe-normalized* bracket
  `jones D w = (-A³)^(-w) ⟨D⟩` is invariant under the first Reidemeister move as well.

`Frontier.jones_polynomial_invariant` collects these four statements.

Finally `Frontier.exists_nontrivial_kauffmanBracket` exhibits a model of the axioms with a
nonzero bracket and with `e 0 ≠ e 1` (built from a two–dimensional representation of the
Temperley–Lieb algebra `TL₃`), so that the axiom system — and hence the main theorem — is not
vacuous.
-/

namespace Frontier

open scoped BigOperators

/-- Kauffman's local skein axioms for a bracket functional on link diagrams. -/
structure KauffmanBracket (R : Type*) [CommRing R] (T : Type*) [Monoid T]
    (D : Type*) (Ctx : Type*) where
  /-- The invertible variable `A`. -/
  A : Rˣ
  /-- The two Temperley–Lieb cap–cup tangles. -/
  e : Fin 2 → T
  /-- Crossings whose `A`-smoothing is the identity tangle. -/
  xp : Fin 2 → T
  /-- Crossings whose `A`-smoothing is the cap–cup tangle. -/
  xm : Fin 2 → T
  /-- Inserting a local tangle into a context produces a diagram. -/
  plug : Ctx → T → D
  /-- A context can absorb a tangle stacked below the hole. -/
  pre : Ctx → T → Ctx
  /-- A context can absorb a tangle stacked above the hole. -/
  post : Ctx → T → Ctx
  plug_pre : ∀ C t s, plug (pre C t) s = plug C (s * t)
  plug_post : ∀ C t s, plug (post C t) s = plug C (t * s)
  /-- Adding a disjoint circle to a diagram. -/
  circle : D → D
  /-- The bracket functional. -/
  br : D → R
  br_circle : ∀ d, br (circle d) = (-(A : R) ^ 2 - ((A⁻¹ : Rˣ) : R) ^ 2) * br d
  skein_xp : ∀ C i, br (plug C (xp i))
      = (A : R) * br (plug C 1) + ((A⁻¹ : Rˣ) : R) * br (plug C (e i))
  skein_xm : ∀ C i, br (plug C (xm i))
      = ((A⁻¹ : Rˣ) : R) * br (plug C 1) + (A : R) * br (plug C (e i))
  plug_ee : ∀ C i, plug C (e i * e i) = circle (plug C (e i))
  tl_zero : e 0 * e 1 * e 0 = e 0
  tl_one : e 1 * e 0 * e 1 = e 1

namespace KauffmanBracket

variable {R : Type*} [CommRing R] {T : Type*} [Monoid T] {D Ctx : Type*}
  (K : KauffmanBracket R T D Ctx)

/-- Shorthand for `A⁻¹` as an element of `R`. -/
def Ai : R := ((K.A⁻¹ : Rˣ) : R)

lemma A_mul_Ai : (K.A : R) * K.Ai = 1 := by
  simp [Ai, ← Units.val_mul]

/-- The value of a disjoint circle, `δ = -A² - A⁻²`. -/
def delta : R := -(K.A : R) ^ 2 - K.Ai ^ 2

/-- The context obtained from `C` by stacking `a` above and `b` below the hole. -/
def ctx (C : Ctx) (a b : T) : Ctx := K.pre (K.post C a) b

@[simp] lemma plug_ctx (C : Ctx) (a b s : T) :
    K.plug (K.ctx C a b) s = K.plug C (a * s * b) := by
  rw [ctx, K.plug_pre, K.plug_post, mul_assoc]

/-- Skein relation for a crossing `xp i` occurring inside a word `a * · * b`. -/
lemma skein_xp' (C : Ctx) (a b : T) (i : Fin 2) :
    K.br (K.plug C (a * K.xp i * b))
      = (K.A : R) * K.br (K.plug C (a * b)) + K.Ai * K.br (K.plug C (a * K.e i * b)) := by
  have := K.skein_xp (K.ctx C a b) i
  simpa [mul_one] using this

/-- Skein relation for a crossing `xm i` occurring inside a word `a * · * b`. -/
lemma skein_xm' (C : Ctx) (a b : T) (i : Fin 2) :
    K.br (K.plug C (a * K.xm i * b))
      = K.Ai * K.br (K.plug C (a * b)) + (K.A : R) * K.br (K.plug C (a * K.e i * b)) := by
  have := K.skein_xm (K.ctx C a b) i
  simpa [mul_one] using this

/-- A doubled cap–cup inside a word produces a factor `δ`. -/
lemma br_ee (C : Ctx) (a b : T) (i : Fin 2) :
    K.br (K.plug C (a * (K.e i * K.e i) * b)) = K.delta * K.br (K.plug C (a * K.e i * b)) := by
  have h := K.plug_ee (K.ctx C a b) i
  rw [plug_ctx] at h
  rw [h, K.br_circle, plug_ctx]
  rfl

/-! ### Reidemeister II -/

/-- **Reidemeister II**: the bracket is invariant under cancelling a pair of opposite
crossings at the same position. -/
theorem br_R2 (C : Ctx) (i : Fin 2) :
    K.br (K.plug C (K.xp i * K.xm i)) = K.br (K.plug C 1) := by
  have h1 : K.br (K.plug C (1 * K.xp i * (K.xm i)))
      = (K.A : R) * K.br (K.plug C (1 * K.xm i))
        + K.Ai * K.br (K.plug C (1 * K.e i * K.xm i)) := K.skein_xp' C 1 (K.xm i) i
  have h2 : K.br (K.plug C (1 * K.xm i * 1))
      = K.Ai * K.br (K.plug C (1 * 1)) + (K.A : R) * K.br (K.plug C (1 * K.e i * 1)) :=
    K.skein_xm' C 1 1 i
  have h3 : K.br (K.plug C (K.e i * K.xm i * 1))
      = K.Ai * K.br (K.plug C (K.e i * 1))
        + (K.A : R) * K.br (K.plug C (K.e i * K.e i * 1)) := K.skein_xm' C (K.e i) 1 i
  have h4 : K.br (K.plug C (1 * (K.e i * K.e i) * 1))
      = K.delta * K.br (K.plug C (1 * K.e i * 1)) := K.br_ee C 1 1 i
  simp only [one_mul, mul_one] at h1 h2 h3 h4
  have hd : K.delta = -(K.A : R) ^ 2 - K.Ai ^ 2 := rfl
  rw [hd] at h4
  rw [h1, h2, h3, h4]
  have hA : (K.A : R) * K.Ai = 1 := K.A_mul_Ai
  linear_combination (K.br (K.plug C 1)
      - ((K.A : R) ^ 2 + K.Ai ^ 2) * K.br (K.plug C (K.e i))) * hA

/-! ### Reidemeister III -/

/-- Expansion of a triple crossing into the Temperley–Lieb basis. -/
lemma br_triple (C : Ctx) (i j : Fin 2) (hij : K.e i * K.e j * K.e i = K.e i) :
    K.br (K.plug C (K.xp i * K.xp j * K.xp i))
      = (K.A : R) ^ 3 * K.br (K.plug C 1)
        + (K.A : R) * K.br (K.plug C (K.e i))
        + (K.A : R) * K.br (K.plug C (K.e j))
        + K.Ai * (K.br (K.plug C (K.e i * K.e j)) + K.br (K.plug C (K.e j * K.e i))) := by
  have hA : (K.A : R) * K.Ai = 1 := K.A_mul_Ai
  have hd : K.delta = -(K.A : R) ^ 2 - K.Ai ^ 2 := rfl
  -- expand the three crossings one after the other
  have h1 : K.br (K.plug C (K.xp i * (K.xp j * K.xp i)))
      = (K.A : R) * K.br (K.plug C (K.xp j * K.xp i))
        + K.Ai * K.br (K.plug C (K.e i * (K.xp j * K.xp i))) := by
    simpa [mul_assoc] using K.skein_xp' C 1 (K.xp j * K.xp i) i
  have h2 : K.br (K.plug C (K.xp j * K.xp i))
      = (K.A : R) * K.br (K.plug C (K.xp i))
        + K.Ai * K.br (K.plug C (K.e j * K.xp i)) := by
    simpa [mul_assoc] using K.skein_xp' C 1 (K.xp i) j
  have h3 : K.br (K.plug C (K.xp i))
      = (K.A : R) * K.br (K.plug C 1) + K.Ai * K.br (K.plug C (K.e i)) := by
    simpa using K.skein_xp' C 1 1 i
  have h4 : K.br (K.plug C (K.e j * K.xp i))
      = (K.A : R) * K.br (K.plug C (K.e j))
        + K.Ai * K.br (K.plug C (K.e j * K.e i)) := by
    simpa using K.skein_xp' C (K.e j) 1 i
  have h5 : K.br (K.plug C (K.e i * (K.xp j * K.xp i)))
      = (K.A : R) * K.br (K.plug C (K.e i * K.xp i))
        + K.Ai * K.br (K.plug C (K.e i * (K.e j * K.xp i))) := by
    simpa [mul_assoc] using K.skein_xp' C (K.e i) (K.xp i) j
  have h6 : K.br (K.plug C (K.e i * K.xp i))
      = (K.A : R) * K.br (K.plug C (K.e i))
        + K.Ai * K.br (K.plug C (K.e i * K.e i)) := by
    simpa using K.skein_xp' C (K.e i) 1 i
  have h7 : K.br (K.plug C (K.e i * (K.e j * K.xp i)))
      = (K.A : R) * K.br (K.plug C (K.e i * K.e j))
        + K.Ai * K.br (K.plug C (K.e i * (K.e j * K.e i))) := by
    simpa [mul_assoc] using K.skein_xp' C (K.e i * K.e j) 1 i
  have h8 : K.br (K.plug C (K.e i * K.e i))
      = (-(K.A : R) ^ 2 - K.Ai ^ 2) * K.br (K.plug C (K.e i)) := by
    have := K.br_ee C 1 1 i
    rw [hd] at this
    simpa using this
  have h9 : K.br (K.plug C (K.e i * (K.e j * K.e i))) = K.br (K.plug C (K.e i)) := by
    rw [← mul_assoc, hij]
  rw [mul_assoc]
  linear_combination h1 + (K.A : R) * h2 + (K.A : R) ^ 2 * h3 + (K.A : R) * K.Ai * h4
    + K.Ai * h5 + K.Ai * (K.A : R) * h6 + K.Ai ^ 2 * h7 + (K.A : R) * K.Ai ^ 2 * h8
    + K.Ai ^ 3 * h9
    + ((K.A : R) * K.br (K.plug C (K.e j)) + K.Ai * K.br (K.plug C (K.e j * K.e i))
        + K.Ai * K.br (K.plug C (K.e i * K.e j))
        - ((K.A : R) * ((K.A : R) * K.Ai - 1) + K.Ai ^ 3) * K.br (K.plug C (K.e i))) * hA

/-- **Reidemeister III**: the bracket is invariant under the third Reidemeister move. -/
theorem br_R3 (C : Ctx) :
    K.br (K.plug C (K.xp 0 * K.xp 1 * K.xp 0)) = K.br (K.plug C (K.xp 1 * K.xp 0 * K.xp 1)) := by
  rw [K.br_triple C 0 1 K.tl_zero, K.br_triple C 1 0 K.tl_one]
  ring

/-! ### Reidemeister I -/

/-- A curl built from an `xm` crossing multiplies the bracket by `-A³`. -/
theorem br_kink_xm (C : Ctx) (i : Fin 2) :
    K.br (K.plug C (K.xm i * K.e i)) = (-(K.A : R) ^ 3) * K.br (K.plug C (K.e i)) := by
  have hA : (K.A : R) * K.Ai = 1 := K.A_mul_Ai
  have h1 : K.br (K.plug C (1 * K.xm i * K.e i))
      = K.Ai * K.br (K.plug C (1 * K.e i))
        + (K.A : R) * K.br (K.plug C (1 * K.e i * K.e i)) := K.skein_xm' C 1 (K.e i) i
  have h2 : K.br (K.plug C (1 * (K.e i * K.e i) * 1))
      = K.delta * K.br (K.plug C (1 * K.e i * 1)) := K.br_ee C 1 1 i
  simp only [one_mul, mul_one] at h1 h2
  have hd : K.delta = -(K.A : R) ^ 2 - K.Ai ^ 2 := rfl
  rw [hd] at h2
  rw [h1, h2]
  linear_combination (-K.Ai * K.br (K.plug C (K.e i))) * hA

/-- A curl built from an `xp` crossing multiplies the bracket by `-A⁻³`. -/
theorem br_kink_xp (C : Ctx) (i : Fin 2) :
    K.br (K.plug C (K.xp i * K.e i)) = (-K.Ai ^ 3) * K.br (K.plug C (K.e i)) := by
  have hA : (K.A : R) * K.Ai = 1 := K.A_mul_Ai
  have h1 : K.br (K.plug C (1 * K.xp i * K.e i))
      = (K.A : R) * K.br (K.plug C (1 * K.e i))
        + K.Ai * K.br (K.plug C (1 * K.e i * K.e i)) := K.skein_xp' C 1 (K.e i) i
  have h2 : K.br (K.plug C (1 * (K.e i * K.e i) * 1))
      = K.delta * K.br (K.plug C (1 * K.e i * 1)) := K.br_ee C 1 1 i
  simp only [one_mul, mul_one] at h1 h2
  have hd : K.delta = -(K.A : R) ^ 2 - K.Ai ^ 2 := rfl
  rw [hd] at h2
  rw [h1, h2]
  linear_combination (-(K.A : R) * K.br (K.plug C (K.e i))) * hA

/-! ### The writhe-normalized bracket -/

/-- The unit `-A³` of `R`. -/
def negA3 : Rˣ := -K.A ^ 3

@[simp] lemma negA3_val : ((K.negA3 : Rˣ) : R) = -(K.A : R) ^ 3 := by
  simp [negA3]

@[simp] lemma negA3_inv_val : (((K.negA3)⁻¹ : Rˣ) : R) = -K.Ai ^ 3 := by
  have h : ((K.negA3)⁻¹ : Rˣ) = -K.A⁻¹ ^ 3 := by
    refine inv_eq_of_mul_eq_one_right ?_
    show (-K.A ^ 3) * (-K.A⁻¹ ^ 3) = 1
    rw [neg_mul_neg, ← mul_pow, mul_inv_cancel, one_pow]
  rw [h]
  simp [Ai]

/-- The writhe-normalized bracket `(-A³)^(-w) ⟨D⟩`, where `w` is the writhe of the diagram.
This is (up to the substitution `A = t^(-1/4)`) the Jones polynomial. -/
def jones (d : D) (w : ℤ) : R := ((K.negA3 ^ (-w) : Rˣ) : R) * K.br d

/-- **Reidemeister I** for the normalized bracket: adding a positive curl (which raises the
writhe by one and multiplies the bracket by `-A³`) does not change the Jones invariant. -/
theorem jones_R1_pos (C : Ctx) (i : Fin 2) (w : ℤ) :
    K.jones (K.plug C (K.xm i * K.e i)) (w + 1) = K.jones (K.plug C (K.e i)) w := by
  have hzp : K.negA3 ^ (-(w + 1)) = K.negA3 ^ (-w) * (K.negA3)⁻¹ := by
    rw [show -(w + 1) = -w + (-1 : ℤ) by ring, zpow_add K.negA3, zpow_neg_one]
  simp only [jones, hzp, K.br_kink_xm C i, Units.val_mul, negA3_inv_val]
  have hA : (K.A : R) * K.Ai = 1 := K.A_mul_Ai
  have h3 : (-K.Ai ^ 3) * (-(K.A : R) ^ 3) = 1 := by
    have : ((K.A : R) * K.Ai) ^ 3 = 1 := by rw [hA, one_pow]
    linear_combination this
  calc ((K.negA3 ^ (-w) : Rˣ) : R) * (-K.Ai ^ 3) * ((-(K.A : R) ^ 3) * K.br (K.plug C (K.e i)))
      = ((K.negA3 ^ (-w) : Rˣ) : R) * ((-K.Ai ^ 3) * (-(K.A : R) ^ 3))
          * K.br (K.plug C (K.e i)) := by ring
    _ = ((K.negA3 ^ (-w) : Rˣ) : R) * K.br (K.plug C (K.e i)) := by rw [h3, mul_one]

/-- **Reidemeister I** for the normalized bracket, negative curl. -/
theorem jones_R1_neg (C : Ctx) (i : Fin 2) (w : ℤ) :
    K.jones (K.plug C (K.xp i * K.e i)) (w - 1) = K.jones (K.plug C (K.e i)) w := by
  have hzp : K.negA3 ^ (-(w - 1)) = K.negA3 ^ (-w) * K.negA3 := by
    rw [show -(w - 1) = -w + (1 : ℤ) by ring, zpow_add K.negA3, zpow_one]
  simp only [jones, hzp, K.br_kink_xp C i, Units.val_mul, negA3_val]
  have hA : (K.A : R) * K.Ai = 1 := K.A_mul_Ai
  have h3 : (-(K.A : R) ^ 3) * (-K.Ai ^ 3) = 1 := by
    have : ((K.A : R) * K.Ai) ^ 3 = 1 := by rw [hA, one_pow]
    linear_combination this
  calc ((K.negA3 ^ (-w) : Rˣ) : R) * (-(K.A : R) ^ 3) * ((-K.Ai ^ 3) * K.br (K.plug C (K.e i)))
      = ((K.negA3 ^ (-w) : Rˣ) : R) * ((-(K.A : R) ^ 3) * (-K.Ai ^ 3))
          * K.br (K.plug C (K.e i)) := by ring
    _ = ((K.negA3 ^ (-w) : Rˣ) : R) * K.br (K.plug C (K.e i)) := by rw [h3, mul_one]

/-- **Reidemeister II** for the normalized bracket (the move does not change the writhe). -/
theorem jones_R2 (C : Ctx) (i : Fin 2) (w : ℤ) :
    K.jones (K.plug C (K.xp i * K.xm i)) w = K.jones (K.plug C 1) w := by
  simp [jones, K.br_R2 C i]

/-- **Reidemeister III** for the normalized bracket (the move does not change the writhe). -/
theorem jones_R3 (C : Ctx) (w : ℤ) :
    K.jones (K.plug C (K.xp 0 * K.xp 1 * K.xp 0)) w
      = K.jones (K.plug C (K.xp 1 * K.xp 0 * K.xp 1)) w := by
  simp [jones, K.br_R3 C]

end KauffmanBracket

/-- **The Jones polynomial is a link invariant.**

For any Kauffman bracket satisfying the local skein axioms, the writhe-normalized bracket
`jones D w = (-A³)^(-w) ⟨D⟩` is invariant under all three Reidemeister moves:

* R1: inserting a positive curl (writhe `w ↦ w + 1`) or a negative curl (writhe `w ↦ w - 1`)
  leaves the invariant unchanged;
* R2: cancelling a pair of opposite crossings leaves it unchanged;
* R3: sliding a strand across a crossing leaves it unchanged.

Since every planar isotopy class of diagrams of a given link is connected to any other by a
finite sequence of these moves (Reidemeister's theorem), this is exactly the well-definedness
of the Jones polynomial as a link invariant. -/
theorem jones_polynomial_invariant
    {R : Type*} [CommRing R] {T : Type*} [Monoid T] {D Ctx : Type*}
    (K : KauffmanBracket R T D Ctx) :
    (∀ (C : Ctx) (i : Fin 2) (w : ℤ),
        K.jones (K.plug C (K.xm i * K.e i)) (w + 1) = K.jones (K.plug C (K.e i)) w) ∧
    (∀ (C : Ctx) (i : Fin 2) (w : ℤ),
        K.jones (K.plug C (K.xp i * K.e i)) (w - 1) = K.jones (K.plug C (K.e i)) w) ∧
    (∀ (C : Ctx) (i : Fin 2) (w : ℤ),
        K.jones (K.plug C (K.xp i * K.xm i)) w = K.jones (K.plug C 1) w) ∧
    (∀ (C : Ctx) (w : ℤ),
        K.jones (K.plug C (K.xp 0 * K.xp 1 * K.xp 0)) w
          = K.jones (K.plug C (K.xp 1 * K.xp 0 * K.xp 1)) w) :=
  ⟨K.jones_R1_pos, K.jones_R1_neg, K.jones_R2, K.jones_R3⟩

/-! ## A model of the axioms

To see that the axiom system above is consistent — and that the theorem is not vacuous — we
exhibit a model built from the two-dimensional representation of the Temperley–Lieb algebra
`TL₃` by `2 × 2` matrices:
`e₀ = !![δ, 1; 0, 0]`, `e₁ = !![0, 0; 1, δ]` with `δ = -A² - A⁻²`, crossings
`x± = A^{±1} • 1 + A^{∓1} • eᵢ`, diagrams = matrices, contexts = pairs of matrices acting by
left/right multiplication, and the bracket given by the matrix trace. -/

open Matrix in
/-- The loop value `δ = -A² - A⁻²`. -/
def loopValue {R : Type*} [CommRing R] (A : Rˣ) : R := -(A : R) ^ 2 - ((A⁻¹ : Rˣ) : R) ^ 2

open Matrix in
/-- The two Temperley–Lieb generators of `TL₃` in their `2 × 2` matrix representation. -/
def tlMat {R : Type*} [CommRing R] (A : Rˣ) : Fin 2 → Matrix (Fin 2) (Fin 2) R :=
  ![!![loopValue A, 1; 0, 0], !![0, 0; 1, loopValue A]]

open Matrix in
lemma tlMat_mul_self {R : Type*} [CommRing R] (A : Rˣ) (i : Fin 2) :
    tlMat A i * tlMat A i = (loopValue A : R) • tlMat A i := by
  fin_cases i <;>
    (simp only [tlMat]
     ext a b
     fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two])

open Matrix in
lemma tlMat_zero_one_zero {R : Type*} [CommRing R] (A : Rˣ) :
    (tlMat A 0 : Matrix (Fin 2) (Fin 2) R) * tlMat A 1 * tlMat A 0 = tlMat A 0 := by
  simp only [tlMat, Matrix.cons_val_zero, Matrix.cons_val_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

open Matrix in
lemma tlMat_one_zero_one {R : Type*} [CommRing R] (A : Rˣ) :
    (tlMat A 1 : Matrix (Fin 2) (Fin 2) R) * tlMat A 0 * tlMat A 1 = tlMat A 1 := by
  simp only [tlMat, Matrix.cons_val_zero, Matrix.cons_val_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

open Matrix in
/-- A model of the Kauffman bracket axioms over an arbitrary commutative ring `R` with an
invertible `A`, built from the `2 × 2` matrix representation of `TL₃`. -/
def matrixModel (R : Type*) [CommRing R] (A : Rˣ) :
    KauffmanBracket R (Matrix (Fin 2) (Fin 2) R) (Matrix (Fin 2) (Fin 2) R)
      (Matrix (Fin 2) (Fin 2) R × Matrix (Fin 2) (Fin 2) R) where
  A := A
  e := tlMat A
  xp := fun i => (A : R) • (1 : Matrix (Fin 2) (Fin 2) R) + ((A⁻¹ : Rˣ) : R) • tlMat A i
  xm := fun i => ((A⁻¹ : Rˣ) : R) • (1 : Matrix (Fin 2) (Fin 2) R) + (A : R) • tlMat A i
  plug := fun C t => C.1 * t * C.2
  pre := fun C t => (C.1, t * C.2)
  post := fun C t => (C.1 * t, C.2)
  plug_pre := by intro C t s; simp [mul_assoc]
  plug_post := by intro C t s; simp [mul_assoc]
  circle := fun d => (loopValue A : R) • d
  br := Matrix.trace
  br_circle := by intro d; simp [loopValue, Matrix.trace_smul, smul_eq_mul]
  skein_xp := by
    intro C i
    simp [Matrix.mul_add, Matrix.add_mul, smul_eq_mul]
  skein_xm := by
    intro C i
    simp [Matrix.mul_add, Matrix.add_mul, smul_eq_mul]
  plug_ee := by
    intro C i
    simp [tlMat_mul_self]
  tl_zero := tlMat_zero_one_zero A
  tl_one := tlMat_one_zero_one A

open Matrix in
/-- The axioms are not vacuous: there is a model in which the two Temperley–Lieb generators
are distinct and the bracket takes a nonzero value (here over `ℚ` with `A = 2`). -/
theorem exists_nontrivial_kauffmanBracket :
    ∃ K : KauffmanBracket ℚ (Matrix (Fin 2) (Fin 2) ℚ) (Matrix (Fin 2) (Fin 2) ℚ)
        (Matrix (Fin 2) (Fin 2) ℚ × Matrix (Fin 2) (Fin 2) ℚ),
      K.e 0 ≠ K.e 1 ∧ K.br (K.plug (1, 1) 1) ≠ 0 := by
  set A : ℚˣ := Units.mk0 2 (by norm_num) with hA
  refine ⟨matrixModel ℚ A, ?_, ?_⟩
  · intro h
    have h' : (tlMat A 0 : Matrix (Fin 2) (Fin 2) ℚ) = tlMat A 1 := h
    have h01 := congrFun (congrFun h' 0) 1
    simp [tlMat] at h01
  · show Matrix.trace ((1 : Matrix (Fin 2) (Fin 2) ℚ) * 1 * 1) ≠ 0
    simp [Matrix.trace_one]

end Frontier

