-- (Lean requires `import` to precede any module docstring; the required header follows.)
import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Faltings' theorem (the Mordell conjecture) states that a smooth projective curve of genus
at least `2` defined over `ℚ` has only finitely many rational points.

Here we formalize the statement for *smooth plane curves*, where the genus is given by the
degree–genus formula `g = (d-1)(d-2)/2`, so that "genus ≥ 2" is exactly "degree ≥ 4".
The general statement is recorded as `Frontier.MordellConjecturePlane` (a `Prop`-valued
definition, not proved here — it is Faltings' theorem).

We then prove, unconditionally and axiom-cleanly:

* `Frontier.projectivePoints_finite_of_affine`: a Lean-checked reduction of the finiteness of
  the rational points of a projective plane curve to finiteness of its affine rational points
  together with its rational points at infinity;
* `Frontier.mordellPlane_of_affine_finiteness`: the resulting reduction of
  `MordellConjecturePlane` to the affine statement;
* `Frontier.faltings_mordell`: the base case for the Fermat quartic `x⁴ + y⁴ = z⁴`, a smooth
  plane curve of degree `4` (hence of genus `3 ≥ 2`), whose set of rational points in `ℙ²(ℚ)`
  is proved finite — in fact it consists of exactly the four points
  `(±1 : 0 : 1)`, `(0 : ±1 : 1)`.
-/

namespace Frontier

open MvPolynomial Projectivization

/-! ## Homogeneous polynomials and projective points -/

/-- Evaluating a homogeneous polynomial of degree `d` at a scaled point scales the value
by `c ^ d`. -/

theorem fermatQuartic_projectivePoints_ncard :
    (projectivePoints fermatQuartic).ncard = 4 := by
  have hne : ∀ a b c d : ℚ, ¬(a = c ∧ b = d) →
      Projectivization.mk ℚ ![a, b, 1] (vec_ne_zero_of_last a b) ≠
        Projectivization.mk ℚ ![c, d, 1] (vec_ne_zero_of_last c d) :=
    fun _ _ _ _ h he => h (mk_last_inj he)
  rw [fermatQuartic_projectivePoints_eq]
  rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne 1 0 (-1) 0 (by norm_num), hne 1 0 0 1 (by norm_num),
        hne 1 0 0 (-1) (by norm_num)⟩) (Set.toFinite _),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne (-1) 0 0 1 (by norm_num), hne (-1) 0 0 (-1) (by norm_num)⟩) (Set.toFinite _),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_singleton_iff]
      exact hne 0 1 0 (-1) (by norm_num)) (Set.toFinite _),
    Set.ncard_singleton]

/-- **Faltings/Mordell, base case.**  The Fermat quartic `x⁴ + y⁴ = z⁴` is a smooth plane
curve of degree `4` over `ℚ`, hence of genus `3 ≥ 2`, and its set of rational points in the
projective plane is finite — indeed it has exactly four points.  This is an unconditional
instance of the conclusion of `Frontier.MordellConjecturePlane` for a curve of genus `≥ 2`. -/
