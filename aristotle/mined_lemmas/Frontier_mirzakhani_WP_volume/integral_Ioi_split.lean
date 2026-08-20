import Mathlib

/-!
# The Fermi–Dirac integral `∫_0^∞ t/(1+e^t) dt = π²/12`

This auxiliary file establishes the elementary integral underlying Mirzakhani's
integration kernel, via the Mellin transform of the Dirichlet eta function.
-/


open Real MeasureTheory Set Complex
open scoped Real

namespace Mirzakhani

/-- Coefficients of the Dirichlet eta series, with the (irrelevant) `n = 0` term set to `0`. -/

lemma integral_Ioi_split {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : IntegrableOn f (Ioi a)) :
    (∫ u in Ioi a, f u) = (∫ u in Ioc a b, f u) + (∫ u in Ioi b, f u) := by
  rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hf.mono_set (fun x hx => hx.1)) (hf.mono_set (fun x hx => lt_of_le_of_lt hab hx)),
    Set.Ioc_union_Ioi_eq_Ioi hab]

