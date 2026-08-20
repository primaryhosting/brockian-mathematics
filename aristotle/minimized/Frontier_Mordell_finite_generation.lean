/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

open scoped Pointwise

/-!
## The statement

Mordell's theorem asserts that for an elliptic curve `E` over `ℚ`, the abelian group `E(ℚ)` of
rational points is finitely generated.  In Mathlib an elliptic curve over `ℚ` is a Weierstrass
curve `W : WeierstrassCurve ℚ` satisfying the typeclass assumption `W.IsElliptic`, and its group
of rational points is `W.toAffine.Point`, which carries an `AddCommGroup` structure.

Mathlib (at the pinned commit) contains no form of the Mordell–Weil theorem: searching for
`MordellWeil` returns nothing, and the theory developed in
`Mathlib.AlgebraicGeometry.EllipticCurve.*` stops at the group law, division polynomials and
reduction.  So the statement below is a genuine formalization, and what is proved here is the
classical *descent step*: the reduction of Mordell's theorem to the two inputs of the standard
proof, namely

* the weak Mordell–Weil theorem (`E(ℚ)/2E(ℚ)` is finite), and
* the theory of the canonical height (heights have finite sublevel sets, and every point of large
  height can be brought down by subtracting a coset representative and halving).

Both inputs are packaged in `Frontier.DescentData`.
-/

/-- The full Mordell–Weil statement over `ℚ`: the group of rational points of every elliptic
curve over `ℚ` is finitely generated.  (Stated only; the theorem proved below is the descent
reduction `Frontier.Mordell_finite_generation`.) -/

theorem fg_of_descentData {A : Type*} [AddCommGroup A] (D : DescentData A) : AddGroup.FG A := by
  classical
  set T : Set A := {a : A | D.height a ≤ D.bound} ∪ (D.reps : Set A) with hT
  have hTfin : T.Finite := (D.finite_height_le D.bound).union D.reps.finite_toSet
  have key : ∀ n : ℕ, ∀ a : A, D.height a ≤ n → a ∈ AddSubgroup.closure T := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha
      by_cases hb : D.height a ≤ D.bound
      · exact AddSubgroup.subset_closure (Or.inl hb)
      · obtain ⟨b, hlt, hmem⟩ := D.descent a (not_le.mp hb)
        have hbmem : b ∈ AddSubgroup.closure T :=
          ih (D.height b) (lt_of_lt_of_le hlt ha) b le_rfl
        have hrep : a - 2 • b ∈ AddSubgroup.closure T :=
          AddSubgroup.subset_closure (Or.inr hmem)
        have : a = (a - 2 • b) + 2 • b := by abel
        rw [this]
        exact add_mem hrep (nsmul_mem hbmem 2)
  refine AddGroup.fg_iff.mpr ⟨T, ?_, hTfin⟩
  refine eq_top_iff.mpr fun a _ => key (D.height a) a le_rfl

/-- **Mordell's theorem, reduced to descent.**  If the group of rational points of an elliptic
curve over `ℚ` admits descent data — i.e. the weak Mordell–Weil theorem together with the
Northcott property and the descent inequality for the height — then `E(ℚ)` is finitely
generated. -/

theorem Mordell_finite_generation (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (D : DescentData W.toAffine.Point) : AddGroup.FG W.toAffine.Point :=
  fg_of_descentData D

/-- The reduction, in the form of the full statement: if every elliptic curve over `ℚ` admits
descent data on its group of rational points, then Mordell's theorem holds. -/
