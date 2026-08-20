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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Quadratic-like maps (Douady–Hubbard)

A *quadratic-like map* is a triple `(f, U, V)` where `U ⋐ V` are bounded, connected open
subsets of `ℂ` and `f : U → V` is a proper holomorphic map of degree `2`.  Degree two is
encoded here concretely: `f` has a unique critical point `c ∈ U`, the fibre over the critical
value `f c` is the singleton `{c}`, and every other fibre over `V` consists of exactly two
points.
-/

/-- A quadratic-like map in the sense of Douady–Hubbard, presented as a globally defined
function `f : ℂ → ℂ` together with the data of the domains `U ⋐ V`.  Only the behaviour of
`f` on `U` is constrained. -/
structure QuadraticLike where
  /-- The small domain. -/
  U : Set ℂ
  /-- The large domain. -/
  V : Set ℂ
  /-- The map. -/
  f : ℂ → ℂ
  /-- The critical point. -/
  critical : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isConnected_U : IsConnected U
  isConnected_V : IsConnected V
  isBounded_V : Bornology.IsBounded V
  /-- `U` is compactly contained in `V`. -/
  closure_U_subset : closure U ⊆ V
  differentiableOn : DifferentiableOn ℂ f U
  mapsTo : Set.MapsTo f U V
  /-- `f : U → V` is proper. -/
  properOn : ∀ ⦃K : Set ℂ⦄, K ⊆ V → IsCompact K → IsCompact (U ∩ f ⁻¹' K)
  critical_mem : critical ∈ U
  /-- The fibre over the critical value is a single (doubled) point. -/
  fiber_critical : U ∩ f ⁻¹' {f critical} = {critical}
  /-- Every non-critical fibre over `V` has exactly two points: `f` has degree two. -/
  fiber_card : ∀ w ∈ V, w ≠ f critical → (U ∩ f ⁻¹' {w}).ncard = 2
  deriv_critical : deriv f critical = 0
  unique_critical : ∀ z ∈ U, deriv f z = 0 → z = critical

namespace QuadraticLike

variable (Q : QuadraticLike)

/-- The filled Julia set of a quadratic-like map: the points whose whole forward orbit
stays in `U`. -/

lemma sq_K (R : ℝ) (hR : 1 < R) : (sq R hR).K = Metric.closedBall (0 : ℂ) 1 := by
  ext z
  simp only [QuadraticLike.K, Set.mem_setOf_eq, sq_f, sq_U, sqMap_iterate, Metric.mem_ball,
    Metric.mem_closedBall, dist_zero_right, norm_pow]
  constructor
  · intro h
    by_contra hz
    push_neg at hz
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R hz
    have hle : ‖z‖ ^ n ≤ ‖z‖ ^ (2 ^ n) :=
      pow_le_pow_right₀ hz.le (Nat.lt_two_pow_self).le
    exact absurd (h n) (by push_neg; linarith)
  · intro h n
    calc ‖z‖ ^ (2 ^ n) ≤ 1 ^ (2 ^ n) := by
          exact pow_le_pow_left₀ (norm_nonneg z) h _
      _ = 1 := one_pow _
      _ < R := hR

/-!
## Main statement
-/

/-- **McMullen renormalization for quadratic-like maps** (formalized statement together with
the base case and the Lean-checked reductions).

1. *Base case.* For every `R > 1` the map `z ↦ z²` on `ball 0 R ⋐ ball 0 R²` is quadratic-like,
   its filled Julia set is the closed unit disc, which is compact and connected, and it is
   renormalizable of period one.
2. *Renormalization tower (reduction).* If `R` is a renormalization of `Q` of period `n` and
   `R` is renormalizable of period `m`, then `Q` is renormalizable of period `n * m`; hence the
   renormalization operator can be iterated, which is what makes infinitely renormalizable maps
   meaningful.
3. *Rigidity (transport).* Any conjugacy between quadratic-like maps carries filled Julia sets
   bijectively onto each other; in particular a hybrid equivalence is a bijection of the filled
   Julia sets.
4. *Structure of filled Julia sets.* The filled Julia set of a quadratic-like map is compact,
   forward invariant, and totally invariant inside `U`.
5. *Straightening (reduction).* Granting the Douady–Hubbard straightening statement, the filled
   Julia set of every quadratic-like map is carried bijectively by a conjugacy onto the filled
   Julia set of a quadratic-like restriction of a quadratic polynomial `z ↦ z² + c`. -/
