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
