import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Frontier

open Set

/-!
## Quadratic-like maps

Following Douady–Hubbard and McMullen (*Complex Dynamics and Renormalization*),
a **quadratic-like map** is a holomorphic proper degree-two branched covering
`f : V → U` between topological disks with `V ⋐ U`, whose unique critical point we
normalise to be `0`.

The structure below records the data and the properties that are used in the
statements proved here: `V ⊆ U` open subsets of `ℂ`, `f` analytic on a neighbourhood
of each point of `V`, `f` maps `V` into `U` and *onto* `U` (properness/surjectivity),
every fibre over `U` has at most two points (degree `≤ 2`), and `0 ∈ V` is a
critical point of `f`.
-/

/-- A quadratic-like map, presented as the data of the two domains `V ⊆ U ⊆ ℂ` and the
holomorphic map `f : V → U`, which is surjective, has fibres of cardinality at most two
and has a critical point at the origin. -/
structure QuadraticLike where
  /-- The map. -/
  f : ℂ → ℂ
  /-- The target (range) disk. -/
  U : Set ℂ
  /-- The source disk, compactly contained in `U` in the classical definition. -/
  V : Set ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  subset_UV : V ⊆ U
  mapsTo : Set.MapsTo f V U
  surjOn : U ⊆ f '' V
  analytic : AnalyticOnNhd ℂ f V
  crit_mem : (0 : ℂ) ∈ V
  deriv_crit : deriv f 0 = 0
  fiber_encard_le_two : ∀ w ∈ U, {z ∈ V | f z = w}.encard ≤ 2

/-- `R` is a **renormalization of period `n`** of the quadratic-like map `Q`: `R` is itself
a quadratic-like map, its underlying map is the `n`-th iterate of `Q`, and its domains are
contained in those of `Q`.  (This is the combinatorial skeleton of McMullen's definition:
`Q.f^[n] : R.V → R.U` is again quadratic-like around the critical point.) -/

def squareQuadraticLike : QuadraticLike where
  f := fun z => z ^ 2
  U := Metric.ball 0 4
  V := Metric.ball 0 2
  isOpen_U := Metric.isOpen_ball
  isOpen_V := Metric.isOpen_ball
  subset_UV := Metric.ball_subset_ball (by norm_num)
  mapsTo := by
    intro z hz
    simp only [mem_ball_zero_iff] at hz ⊢
    have : ‖z ^ 2‖ = ‖z‖ ^ 2 := by simp
    rw [this]
    nlinarith [norm_nonneg z]
  surjOn := by
    intro w hw
    simp only [mem_ball_zero_iff] at hw
    obtain ⟨r, hr⟩ : ∃ r : ℂ, r ^ 2 = w := IsSepClosed.exists_pow_nat_eq w 2
    refine ⟨r, ?_, hr⟩
    simp only [mem_ball_zero_iff]
    have hnr : ‖r‖ ^ 2 = ‖w‖ := by rw [← hr]; simp
    nlinarith [norm_nonneg r]
  analytic := fun z _ => (analyticAt_id).pow 2
  crit_mem := by simp
  deriv_crit := by simp
  fiber_encard_le_two := fun w _ => sq_fiber_encard_le_two w _

/-!
## Non-degeneracy: the degree-two condition really bites

No quadratic-like map can have underlying map `z ↦ z⁴` (near the critical point such a map
is four-to-one).  Consequently the model map `z ↦ z²` is *not* renormalizable of period `2`,
which matches the fact that `c = 0` is not a renormalizable parameter.
-/

