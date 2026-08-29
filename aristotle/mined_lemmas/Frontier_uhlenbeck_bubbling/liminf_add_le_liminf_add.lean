import Mathlib
/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Formalisation of the *bubbling* (energy concentration) part of Uhlenbeck's
compactness theory for Yang–Mills connections.

Setting.  Let `X` be a metric measure space (think of a Riemannian four-manifold
with its volume measure `μ`) and let `A n` be a sequence of connections with
curvature `F_{A n}`.  All that enters the concentration analysis is the sequence
of energy densities `F n x = |F_{A n}(x)|²`, together with the uniform energy
bound `∫ |F_{A n}|² dμ ≤ Λ`.

A point `x` is an *`ε`-bubble point* of the sequence if, no matter how small a
ball we take around `x`, at least `ε` units of energy persistently sit inside
that ball, i.e. `ε ≤ liminf_n ∫_{B(x,r)} |F_{A n}|²`.  (Using `liminf` is the
same as passing to a subsequence along which the local energies converge, which
is how the statement is usually phrased; with `limsup` instead the statement is
*false*, see `Frontier.limsup_concentration_counterexample` below.)

Main result (`Frontier.uhlenbeck_bubbling`): the set of `ε`-bubble points is
finite, and the number of bubbles is controlled by the energy:
`(number of bubbles) * ε ≤ Λ`.  In particular at most `⌊Λ/ε⌋` bubbles can form,
and if the total energy is below the threshold `ε` no bubbling occurs at all.
-/

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology

namespace Frontier

section Auxiliary

/-- Superadditivity of `liminf` for two `ℝ≥0∞`-valued sequences. -/

theorem liminf_add_le_liminf_add (u v : ℕ → ℝ≥0∞) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n => u n + v n) atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat,
    Filter.liminf_eq_iSup_iInf_of_nat]
  refine ENNReal.iSup_add_iSup_le fun i j => ?_
  refine le_iSup_of_le (max i j) (le_iInf₂ fun m hm => ?_)
  exact add_le_add (iInf₂_le m (le_of_max_le_left hm)) (iInf₂_le m (le_of_max_le_right hm))

/-- Superadditivity of `liminf` for a finite sum of `ℝ≥0∞`-valued sequences. -/
