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

noncomputable def BTerm (V : ℕ → Multiset ℝ → ℝ) (g : ℕ) (rest : Multiset ℝ) (t : ℝ) : ℝ :=
  (1 / 2) * (rest.map fun Lj => ∫ x in Ioi (0:ℝ),
      x * (Mirzakhani.H x (t + Lj) + Mirzakhani.H x (t - Lj)) * V g (x ::ₘ rest.erase Lj)).sum

/-- **Mirzakhani's recursion for Weil–Petersson volumes.**

`V g s` models the Weil–Petersson volume `V_{g,n}(s)` of the moduli space of genus `g`
hyperbolic surfaces with `n = |s|` geodesic boundary components of lengths given by `s`.
The predicate collects the two base cases (a pair of pants and a one-holed torus) together with
Mirzakhani's integral recursion, in its integrated form, for all stable `(g, n)` beyond the base
cases; the continuity requirement records that volumes depend continuously (indeed
polynomially) on the boundary lengths. -/
structure WPVolumeRecursion (V : ℕ → Multiset ℝ → ℝ) : Prop where
  /-- Volumes depend continuously on each boundary length. -/
  continuous_boundary : ∀ (g : ℕ) (s : Multiset ℝ), Continuous fun L => V g (L ::ₘ s)
  /-- Base case: the moduli space of pairs of pants is a point, `V_{0,3} = 1`. -/
  pair_of_pants : ∀ a b c : ℝ, V 0 {a, b, c} = 1
  /-- Base case: `V_{1,1}(L) = (L² + 4π²)/24`. -/
  one_holed_torus : ∀ a : ℝ, V 1 {a} = (a ^ 2 + 4 * π ^ 2) / 24
  /-- Mirzakhani's recursion, in integrated form, in the stable range beyond the base cases. -/
  recursion : ∀ (g : ℕ) (rest : Multiset ℝ) (L : ℝ), 4 ≤ 2 * g + (Multiset.card rest + 1) →
      L * V g (L ::ₘ rest) =
        ∫ t in (0:ℝ)..L, (AconTerm V g rest t + AdconTerm V g rest t + BTerm V g rest t)

/-- Any volume function obeying the recursion assigns the value `1` to every three-holed
sphere. -/
