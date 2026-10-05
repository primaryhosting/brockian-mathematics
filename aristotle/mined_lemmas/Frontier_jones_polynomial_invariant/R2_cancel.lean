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
