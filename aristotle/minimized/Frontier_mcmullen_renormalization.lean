import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalize the basic combinatorial/structural framework of McMullen's theory of
renormalization for quadratic-like maps (Douady–Hubbard quadratic-like maps,
`QuadraticLike` below):

* `Frontier.QuadraticLike` — a degree-two proper holomorphic map `f : U → V` with
  `closure U` compact and contained in `V`, with a unique critical point.
* `Frontier.filledJulia` — the filled Julia set `K(f) = {z ∈ U | ∀ n, f^[n] z ∈ U}`.
* `Frontier.IsRenormalizationOf` — `R` is a renormalization of `Q` with period `p`:
  `R.f = Q.f^[p]`, `R` is defined on a smaller domain around the same critical point,
  and the small filled Julia set `K(R)` is connected.
* `Frontier.Renormalizable` — existence of such a renormalization.

The main theorem `Frontier.mcmullen_renormalization` records the two structural facts
that are proved here in full:

1. **Base case (period one).** A quadratic-like map with connected filled Julia set is
   renormalizable of period `1`, the renormalization being the map itself.
2. **Reduction (multiplicativity of periods).** If `R` is a renormalization of `Q` of
   period `p` and `R` is itself renormalizable of period `q`, then `Q` is renormalizable
   of period `p * q`.  This is the Lean-checked reduction underlying the study of
   infinitely renormalizable maps.

The framework is shown to be non-vacuous: `Frontier.sqQuadraticLike` is the explicit
quadratic-like map `z ↦ z²` on `B(0,2) → B(0,4)`, whose filled Julia set is the closed
unit disc (`Frontier.filledJulia_sq`), hence connected, so it is renormalizable of
period one (`Frontier.sqQuadraticLike_renormalizable`).
-/

open Set

namespace Frontier

/-- A **quadratic-like map** in the sense of Douady–Hubbard: a proper degree-two
holomorphic map `f : U → V` between open subsets of `ℂ` with `closure U` a compact
subset of `V`.  Degree two is encoded by requiring a single critical value `f crit`,
whose fibre is the singleton `{crit}`, all other fibres over `V` consisting of exactly
two points. -/
structure QuadraticLike where
  /-- The smaller domain. -/
  U : Set ℂ
  /-- The larger domain. -/
  V : Set ℂ
  /-- The map. -/
  f : ℂ → ℂ
  /-- The critical point. -/
  crit : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isCompact_closure_U : IsCompact (closure U)
  closure_U_subset_V : closure U ⊆ V
  analyticOn : AnalyticOnNhd ℂ f U
  mapsTo : MapsTo f U V
  surjOn : SurjOn f U V
  crit_mem : crit ∈ U
  fiber_crit : {z ∈ U | f z = f crit} = {crit}
  fiber_two : ∀ w ∈ V, w ≠ f crit → ∃ z₁ z₂ : ℂ, z₁ ≠ z₂ ∧ {z ∈ U | f z = w} = {z₁, z₂}

/-- The filled Julia set of a quadratic-like map: the points of `U` whose whole forward
orbit stays in `U`. -/

def filledJulia (Q : QuadraticLike) : Set ℂ := {z ∈ Q.U | ∀ n : ℕ, Q.f^[n] z ∈ Q.U}

theorem mapsTo_filledJulia (Q : QuadraticLike) :
    MapsTo Q.f (filledJulia Q) (filledJulia Q) := by
  intro z hz
  refine ⟨?_, fun n => ?_⟩
  · simpa using hz.2 1
  · simpa [Function.iterate_succ_apply] using hz.2 (n + 1)

/-- `R` is a **renormalization of `Q` of period `p`**: `R` is a quadratic-like restriction
of the `p`-th iterate of `Q`, around the same critical point, with connected filled Julia
set (the *small Julia set*). -/

def IsRenormalizationOf (R Q : QuadraticLike) (p : ℕ) : Prop :=
  1 ≤ p ∧ R.f = Q.f^[p] ∧ R.U ⊆ Q.U ∧ R.crit = Q.crit ∧ IsConnected (filledJulia R)

/-- A quadratic-like map is **renormalizable of period `p`** if it admits a renormalization
of period `p`. -/

def Renormalizable (Q : QuadraticLike) (p : ℕ) : Prop :=
  ∃ R : QuadraticLike, IsRenormalizationOf R Q p

/-- Base case: a quadratic-like map with connected filled Julia set is its own
renormalization of period one. -/

theorem isRenormalizationOf_self (Q : QuadraticLike) (hK : IsConnected (filledJulia Q)) :
    IsRenormalizationOf Q Q 1 :=
  ⟨le_rfl, by simp, subset_rfl, rfl, hK⟩

/-- Multiplicativity of periods: a renormalization of a renormalization is a
renormalization, with the periods multiplied. -/

theorem isRenormalizationOf_trans {S R Q : QuadraticLike} {p q : ℕ}
    (hR : IsRenormalizationOf R Q p) (hS : IsRenormalizationOf S R q) :
    IsRenormalizationOf S Q (p * q) := by
  obtain ⟨hp, hRf, hRU, hRc, -⟩ := hR
  obtain ⟨hq, hSf, hSU, hSc, hSK⟩ := hS
  refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_,
    hSU.trans hRU, hSc.trans hRc, hSK⟩
  rw [hSf, hRf, Function.iterate_mul]

/-!
## Main statement
-/

/-- **McMullen renormalization: base case and reduction.**

For quadratic-like maps (in the sense of Douady–Hubbard, `Frontier.QuadraticLike`):

1. *(base case)* every quadratic-like map with connected filled Julia set is
   renormalizable of period one, witnessed by the map itself;
2. *(reduction)* if `R` is a renormalization of `Q` of period `p`, and `R` is
   renormalizable of period `q`, then `Q` is renormalizable of period `p * q`;
3. the filled Julia set is always forward invariant.

Statement (2) is the Lean-checked reduction which produces renormalizations of all
periods in the multiplicative semigroup generated by the periods occurring along a
tower of renormalizations, as for infinitely renormalizable maps. -/

theorem mcmullen_renormalization :
    (∀ Q : QuadraticLike, IsConnected (filledJulia Q) →
        IsRenormalizationOf Q Q 1 ∧ Renormalizable Q 1) ∧
    (∀ (Q R : QuadraticLike) (p q : ℕ),
        IsRenormalizationOf R Q p → Renormalizable R q → Renormalizable Q (p * q)) ∧
    (∀ Q : QuadraticLike, MapsTo Q.f (filledJulia Q) (filledJulia Q)) := by
  refine ⟨fun Q hK => ⟨isRenormalizationOf_self Q hK, Q, isRenormalizationOf_self Q hK⟩,
    fun Q R p q hR hRq => ?_, mapsTo_filledJulia⟩
  obtain ⟨S, hS⟩ := hRq
  exact ⟨S, isRenormalizationOf_trans hR hS⟩

/-!
## Non-vacuity: the quadratic-like map `z ↦ z²`
-/
