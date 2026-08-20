/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
(The header above is a plain block comment rather than a module docstring, since Lean 4
does not allow a module docstring to precede the `import` commands.)

# Mordell's theorem: finite generation of `E(ℚ)`

We formalize the statement that the group of rational points of an elliptic curve over `ℚ`
is finitely generated, and we prove the *descent step* of the classical proof: an abelian
group equipped with a height function satisfying the standard axioms and whose quotient by
`2A` is finite is finitely generated.  Specializing to `E(ℚ)` gives
`Frontier.Mordell_finite_generation`, a Lean-checked reduction of Mordell's theorem to the
weak Mordell–Weil theorem together with the existence of a height function.
-/

namespace Frontier

universe u

/-- Abstract height data on an abelian group `A`, modelled on the naive/canonical height
of an elliptic curve over `ℚ`:

* the height is nonnegative;
* there are only finitely many points of bounded height (Northcott property);
* translation by a fixed point distorts the height by a bounded factor;
* duplication multiplies the height by roughly `4`.
-/
structure HeightFunction (A : Type u) [AddCommGroup A] where
  /-- The height function itself. -/
  toFun : A → ℝ
  /-- Heights are nonnegative. -/
  nonneg : ∀ P, 0 ≤ toFun P
  /-- Northcott property: finitely many points of bounded height. -/
  finite_of_le : ∀ C : ℝ, {P : A | toFun P ≤ C}.Finite
  /-- Quasi-additivity of the height under translation by a fixed point. -/
  translate : ∀ Q : A, ∃ c : ℝ, ∀ P : A, toFun (P + Q) ≤ 2 * toFun P + c
  /-- Quasi-quadraticity of the height under duplication. -/
  duplication : ∃ c : ℝ, ∀ P : A, 4 * toFun P ≤ toFun (2 • P) + c

/-- The subgroup `2A` of an abelian group `A`. -/

theorem fg_of_heightFunction_of_weakMordellWeil {A : Type u} [AddCommGroup A]
    (h : HeightFunction A) (hw : WeakMordellWeil A) : AddGroup.FG A := by
  classical
  obtain ⟨R, hR⟩ := exists_reps hw
  obtain ⟨B, hB0, hstep⟩ := descent_step h R hR
  set G : Set A := (R : Set A) ∪ {P : A | h.toFun P ≤ B} with hG
  have hGfin : G.Finite := (R.finite_toSet).union (h.finite_of_le B)
  refine AddGroup.fg_iff.mpr ⟨G, ?_, hGfin⟩
  rw [eq_top_iff]
  intro P₀ _
  by_contra hP₀
  set X : Set A := {T : A | h.toFun T ≤ h.toFun P₀ ∧ T ∉ AddSubgroup.closure G} with hX
  have hXfin : X.Finite :=
    (h.finite_of_le (h.toFun P₀)).subset (fun x hx => hx.1)
  have hXne : X.Nonempty := ⟨P₀, le_rfl, hP₀⟩
  obtain ⟨P, hPX, hPmin⟩ := Set.exists_min_image X h.toFun hXfin hXne
  have hPclos : P ∉ AddSubgroup.closure G := hPX.2
  have hPB : B < h.toFun P := by
    by_contra hcon
    push_neg at hcon
    exact hPclos (AddSubgroup.subset_closure (Or.inr hcon))
  obtain ⟨Q, hQ, S, hPS, hSlt⟩ := hstep P hPB
  have hSclos : S ∈ AddSubgroup.closure G := by
    by_contra hScon
    have hSX : S ∈ X := ⟨le_trans hSlt.le hPX.1, hScon⟩
    exact absurd (hPmin S hSX) (not_le.mpr hSlt)
  have hQclos : Q ∈ AddSubgroup.closure G :=
    AddSubgroup.subset_closure (Or.inl (by exact_mod_cast hQ))
  exact hPclos (hPS ▸ AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hSclos 2) hQclos)

/-- A height function on `ℤ`, showing that the hypotheses of the descent theorem are
satisfiable (and hence that the theorem is not vacuous): `h k = k ^ 2`. -/
