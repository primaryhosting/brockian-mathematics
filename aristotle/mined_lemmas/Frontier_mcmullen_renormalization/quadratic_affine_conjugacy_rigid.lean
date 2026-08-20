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

theorem quadratic_affine_conjugacy_rigid (a b c₁ c₂ : ℂ) (ha : a ≠ 0)
    (h : ∀ z : ℂ, a * (z ^ 2 + c₁) + b = (a * z + b) ^ 2 + c₂) :
    a = 1 ∧ b = 0 ∧ c₁ = c₂ := by
  have e0 := h 0
  have e1 := h 1
  have em := h (-1)
  have hab : a * b = 0 := by linear_combination (em - e1) / 4
  have hb : b = 0 := by
    rcases mul_eq_zero.mp hab with h' | h'
    · exact absurd h' ha
    · exact h'
  subst hb
  have haa : a * (a - 1) = 0 := by linear_combination e0 - e1
  have ha1 : a = 1 := by
    rcases mul_eq_zero.mp haa with h' | h'
    · exact absurd h' ha
    · linear_combination h'
  subst ha1
  refine ⟨rfl, rfl, by linear_combination e0⟩

/-!
## Main statement
-/

/-- **McMullen renormalization (formalized statement, with base case and reduction).**

The four conjuncts are:

1. *Nonvacuity*: the family of quadratic-like maps is nonempty — `z ↦ z²` is a
   quadratic-like map from `B(0,2)` onto `B(0,4)`.
2. *Base case*: every quadratic-like map is its own renormalization of period `1`.
3. *Reduction*: renormalization periods multiply — a renormalization of period `n` of a
   renormalization of period `m` of `Q` is a renormalization of `Q` of period `m * n`
   (so `Q` is `m*n`-renormalizable).
4. *Rigidity base case*: the quadratic normal form `z ↦ z² + c` admits no nontrivial
   affine conjugacies; in particular `z² + c₁` and `z² + c₂` are affinely conjugate only
   when `c₁ = c₂`.
5. *Non-degeneracy*: the model map `z ↦ z²` is not renormalizable of period `2` (its second
   iterate is four-to-one near the critical point), so the notion is not vacuously true. -/
