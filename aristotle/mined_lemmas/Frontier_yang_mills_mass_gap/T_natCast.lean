/-
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open scoped InnerProductSpace

/-!
## The framework

We work in the Osterwalder–Schrader / transfer-matrix (Hamiltonian) picture of a
Euclidean quantum field theory on `ℝ⁴ = ℝ_time × ℝ³`.  The data of such a theory is

* a complex Hilbert space `Hil` of states,
* a distinguished normalised vacuum vector,
* the Euclidean time evolution semigroup `T t = e^{-t H}` (`t ≥ 0`), consisting of
  self-adjoint contractions fixing the vacuum,
* a unitary representation of the group `ℝ³` of space translations, commuting with the
  time evolution and fixing the vacuum,
* a compact gauge group `G` acting by unitaries (the global symmetry group left over
  from the local gauge symmetry) commuting with the space-time symmetries.

A *mass gap* `Δ > 0` is the statement that the Euclidean time evolution decays
exponentially at rate `Δ` on the orthogonal complement of the vacuum, i.e. that the
Hamiltonian `H = -log T` has spectrum contained in `{0} ∪ [Δ, ∞)`.
-/

/-- Data and axioms of a Euclidean quantum field theory on `ℝ⁴` in the
transfer-matrix (Osterwalder–Schrader) picture, together with a global gauge symmetry
group. -/
structure EuclideanQFT where
  /-- The Hilbert space of states. -/
  Hil : Type
  [instNormed : NormedAddCommGroup Hil]
  [instInner : InnerProductSpace ℂ Hil]
  [instComplete : CompleteSpace Hil]
  /-- The vacuum state. -/
  vacuum : Hil
  /-- The vacuum is a unit vector. -/
  vacuum_norm : ‖vacuum‖ = 1
  /-- Euclidean time evolution `T t = e^{-t H}`, only constrained for `t ≥ 0`. -/
  T : ℝ → (Hil →L[ℂ] Hil)
  /-- `T 0 = 1`. -/
  T_zero : T 0 = ContinuousLinearMap.id ℂ Hil
  /-- The semigroup law `T (s + t) = T s ∘ T t`. -/
  T_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)
  /-- Each `T t` is self-adjoint (reflection positivity of the Euclidean measure). -/
  T_selfAdjoint : ∀ t : ℝ, 0 ≤ t → IsSelfAdjoint (T t)
  /-- Each `T t` is a contraction (positivity of the energy). -/
  T_norm_le : ∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1
  /-- The vacuum is invariant under time evolution: it has zero energy. -/
  T_vacuum : ∀ t : ℝ, 0 ≤ t → T t vacuum = vacuum
  /-- The unitary representation of the group `ℝ³` of space translations. -/
  U : (Fin 3 → ℝ) → (Hil ≃ₗᵢ[ℂ] Hil)
  /-- `U` is a representation of `ℝ³`. -/
  U_add : ∀ x y, U (x + y) = (U y).trans (U x)
  /-- Space translations fix the vacuum. -/
  U_vacuum : ∀ x, U x vacuum = vacuum
  /-- Space translations commute with the time evolution: full Euclidean covariance. -/
  U_comm_T : ∀ x, ∀ t : ℝ, 0 ≤ t → ∀ ψ, U x (T t ψ) = T t (U x ψ)
  /-- The smeared local observables of the theory: to a real Schwartz test function on
  space-time `ℝ⁴` is associated an operator on the Hilbert space (a gauge-invariant
  smeared field, e.g. a smeared Wilson loop or field-strength-squared operator). -/
  obs : SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℝ → (Hil →L[ℂ] Hil)
  /-- The smeared observables depend linearly on the test function. -/
  obs_add : ∀ f g, obs (f + g) = obs f + obs g
  /-- Observables are (essentially) self-adjoint: they are real observables. -/
  obs_selfAdjoint : ∀ f, IsSelfAdjoint (obs f)
  /-- The vacuum is cyclic for the algebra of local observables: every state of the
  theory is approximated by local excitations of the vacuum. -/
  vacuum_cyclic :
    (Submodule.span ℂ (Set.range fun f => obs f vacuum)).topologicalClosure = ⊤
  /-- The global gauge symmetry group. -/
  G : Type
  [instGroup : Group G]
  /-- The unitary action of the gauge group. -/
  gauge : G → (Hil ≃ₗᵢ[ℂ] Hil)
  /-- The gauge action is a group action. -/
  gauge_mul : ∀ g h, gauge (g * h) = (gauge h).trans (gauge g)
  /-- The gauge group fixes the vacuum: the symmetry is unbroken. -/
  gauge_vacuum : ∀ g, gauge g vacuum = vacuum
  /-- The gauge action commutes with time evolution. -/
  gauge_comm_T : ∀ g, ∀ t : ℝ, 0 ≤ t → ∀ ψ, gauge g (T t ψ) = T t (gauge g ψ)

attribute [instance] EuclideanQFT.instNormed EuclideanQFT.instInner
  EuclideanQFT.instComplete EuclideanQFT.instGroup

namespace EuclideanQFT

variable (Q : EuclideanQFT)

/-- The physical (vacuum-orthogonal) states of the theory. -/

theorem T_natCast : ∀ n : ℕ, Q.T n = (Q.T 1) ^ n
  | 0 => by simpa using Q.T_zero
  | (n + 1) => by
      have h : ((n : ℝ) + 1) = (1 : ℝ) + (n : ℝ) := by ring
      have := Q.T_add 1 n zero_le_one (Nat.cast_nonneg n)
      push_cast
      rw [h, this, T_natCast n, pow_succ']
      rfl

/-- Iterating the one-step contraction bound. -/
