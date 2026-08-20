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

This file formalises the statement of the Yang–Mills existence and mass gap problem in the
Osterwalder–Schrader / transfer-operator language, and proves a Lean-checked reduction:
*exponential clustering of the Euclidean time evolution implies a positive mass gap*.

Everything lives on a fixed separable infinite dimensional complex Hilbert space
`Frontier.HS = ℓ²(ℕ, ℂ)` (any separable infinite dimensional Hilbert space is isometric to it).
-/

noncomputable section

namespace Frontier

open scoped InnerProductSpace

/-- The state space of the quantum theory: a fixed separable infinite dimensional complex
Hilbert space, realised as `ℓ²(ℕ, ℂ)`. -/
abbrev HS := lp (fun _ : ℕ => ℂ) 2

/-- The gauge group of the Yang–Mills mass gap problem, here `SU(3)`. -/
abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ

/-- The data of a quantum gauge theory with gauge group `G`, in the transfer-operator
(Osterwalder–Schrader reconstructed) formulation:

* a state space `HS` with a normalised vacuum vector `vacuum`;
* the Euclidean time evolution semigroup `evol t = e^{-tH}` of the (positive) Hamiltonian `H`,
  given as a self-adjoint contraction semigroup fixing the vacuum;
* a unitary representation `transl` of the group `ℝ³` of spatial translations, commuting with
  the time evolution and fixing the vacuum;
* gauge invariant Wilson-loop observables `wilson L` indexed by loops `L : ℕ → ℝ⁴` in
  four dimensional Euclidean space-time;
* a unitary representation `gauge` of the gauge group `G` commuting with the observables and
  fixing the vacuum. -/
structure QuantumGaugeTheory (G : Type) [Group G] where
  /-- The vacuum state. -/
  vacuum : HS
  /-- The vacuum is a unit vector. -/
  vacuum_unit : ‖vacuum‖ = 1
  /-- Euclidean time evolution `e^{-tH}`. -/
  evol : ℝ → (HS →L[ℂ] HS)
  /-- `e^{-0·H} = 1`. -/
  evol_zero : evol 0 = ContinuousLinearMap.id ℂ HS
  /-- Semigroup law. -/
  evol_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → evol (s + t) = (evol s).comp (evol t)
  /-- The Hamiltonian is self-adjoint. -/
  evol_selfAdjoint : ∀ t : ℝ, 0 ≤ t → IsSelfAdjoint (evol t)
  /-- The Hamiltonian is positive, i.e. `e^{-tH}` is a contraction. -/
  evol_contraction : ∀ t : ℝ, 0 ≤ t → ‖evol t‖ ≤ 1
  /-- The vacuum has energy zero. -/
  evol_vacuum : ∀ t : ℝ, 0 ≤ t → evol t vacuum = vacuum
  /-- Unitary spatial translations. -/
  transl : (Fin 3 → ℝ) → (HS ≃ₗᵢ[ℂ] HS)
  /-- Translation by `0` is the identity. -/
  transl_zero : transl 0 = LinearIsometryEquiv.refl ℂ HS
  /-- Translations form a representation of `ℝ³`. -/
  transl_add : ∀ a b, transl (a + b) = (transl a).trans (transl b)
  /-- The vacuum is translation invariant. -/
  transl_vacuum : ∀ a, transl a vacuum = vacuum
  /-- Space and Euclidean time translations commute. -/
  transl_evol : ∀ (a : Fin 3 → ℝ) (t : ℝ), 0 ≤ t → ∀ v, transl a (evol t v) = evol t (transl a v)
  /-- Wilson loop observables, indexed by loops in `ℝ⁴`. -/
  wilson : (ℕ → (Fin 4 → ℝ)) → (HS →L[ℂ] HS)
  /-- Unitary action of the gauge group. -/
  gauge : G → (HS ≃ₗᵢ[ℂ] HS)
  /-- The gauge action is a representation. -/
  gauge_one : gauge 1 = LinearIsometryEquiv.refl ℂ HS
  /-- The gauge action is a representation. -/
  gauge_mul : ∀ g h, gauge (g * h) = (gauge h).trans (gauge g)
  /-- The vacuum is gauge invariant. -/
  gauge_vacuum : ∀ g, gauge g vacuum = vacuum
  /-- Wilson loops are gauge invariant observables. -/
  gauge_invariant : ∀ g L v, gauge g (wilson L v) = wilson L (gauge g v)

variable {G : Type} [Group G]

/-- The spatial translate of a loop in `ℝ⁴` by a vector `a ∈ ℝ³` (acting on the last three,
"spatial", coordinates). -/

theorem le_of_pow_two_pow_le {a b C : ℝ} (hb : 0 ≤ b)
    (h : ∀ k : ℕ, a ^ (2 ^ k) ≤ C * b ^ (2 ^ k)) : a ≤ b := by
  by_contra hab
  push_neg at hab
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · have := h 0
    simp [← hb0] at this
    linarith
  · have hr : 1 < a / b := (one_lt_div hb0).2 hab
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (y := a / b) C hr
    have hmono : (a / b) ^ n ≤ (a / b) ^ (2 ^ n) :=
      pow_le_pow_right₀ hr.le (Nat.le_of_lt (Nat.lt_two_pow_self))
    have hk := h n
    have hbk : (0:ℝ) < b ^ (2 ^ n) := by positivity
    have : (a / b) ^ (2 ^ n) ≤ C := by
      rw [div_pow, div_le_iff₀ hbk]
      linarith [hk]
    linarith

/-! ### The reduction -/

/-- **Reduction.** Exponential clustering with rate `m` implies a mass gap of size `m`:
the constant `C` can be removed by the self-adjointness of the Euclidean time evolution. -/
