/-
  Aristotle target (CORRECTED) — CONTINUOUS bounded V ⇒ limit-point at ∞.

  The previous target (proj 17ad1895) was refuted: "bounded" alone is too weak for the
  strong pointwise `IsSolution` — the Dirichlet potential (bounded, but wildly
  discontinuous) forces every classical solution to 0. The fix, per that counterexample,
  is to require V CONTINUOUS. For a continuous bounded potential and non-real λ the
  equation −y″ + V y = λ y is genuinely limit-point at +∞.

  GOAL: replace every `sorry` with a complete Lean 4 / Mathlib proof. No
  sorry/admit/axiom/native_decide; no raised maxHeartbeats; do NOT weaken statements;
  #print axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

open MeasureTheory Filter Topology

namespace Brockian.Weyl.BoundedVContTarget

/-- `y` solves `−y″ + V y = λ y`, i.e. `y″ = (V − λ) y`, on ℝ (complex-valued). -/
structure IsSolution (V : ℝ → ℝ) (lam : ℂ) (y y' y'' : ℝ → ℂ) : Prop where
  deriv1 : ∀ x, HasDerivAt y (y' x) x
  deriv2 : ∀ x, HasDerivAt y' (y'' x) x
  eqn    : ∀ x, y'' x = ((V x : ℂ) - lam) * y x

/-- Square-integrable near `+∞`. -/
def L2NearInfty (y : ℝ → ℂ) : Prop :=
  ∃ a : ℝ, IntegrableOn (fun x => ‖y x‖ ^ 2) (Set.Ici a)

/-- Limit-point case at `+∞`: some nontrivial solution is not L² near `+∞`. -/
def IsLimitPointAtInfty (V : ℝ → ℝ) (lam : ℂ) : Prop :=
  ∃ y y' y'' : ℝ → ℂ, IsSolution V lam y y' y'' ∧ (∃ x, y x ≠ 0) ∧ ¬ L2NearInfty y

/-- **Target.** For a CONTINUOUS bounded real potential and a non-real spectral
parameter, the equation is limit-point at `+∞`. -/
theorem contBoundedV_isLimitPoint (V : ℝ → ℝ) (hVc : Continuous V)
    (M : ℝ) (hV : ∀ x, |V x| ≤ M) (lam : ℂ) (hlam : lam.im ≠ 0) :
    IsLimitPointAtInfty V lam := by
  sorry

end Brockian.Weyl.BoundedVContTarget
