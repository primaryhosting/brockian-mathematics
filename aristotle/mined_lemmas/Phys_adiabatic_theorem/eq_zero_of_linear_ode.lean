import Mathlib
/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A homogeneous linear ODE `w' t = A t (w t)` with continuous (operator valued) coefficient
and vanishing initial datum has only the zero solution. -/

theorem eq_zero_of_linear_ode {A : ℝ → (E →L[ℂ] E)} (hA : Continuous A) {w : ℝ → E}
    (hw : ∀ t, HasDerivAt w (A t (w t)) t) {t₀ : ℝ} (h0 : w t₀ = 0) (t : ℝ) : w t = 0 := by
  set a : ℝ := min t t₀ - 1 with ha
  set b : ℝ := max t t₀ + 1 with hb
  have hab : a ≤ b := by
    have h1 : min t t₀ ≤ max t t₀ := min_le_max
    simp only [ha, hb]; linarith
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hA.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (A a)) (hC a ⟨le_rfl, hab⟩)
  have hmemIoo : ∀ x : ℝ, x ∈ Set.Ioo a b → x ∈ Set.Icc a b := fun x hx => ⟨hx.1.le, hx.2.le⟩
  have hlip : ∀ s ∈ Set.Ioo a b,
      LipschitzOnWith ⟨C, hC0⟩ (fun x : E => A s x) (Set.univ : Set E) := by
    intro s hs
    refine (LipschitzWith.weaken (A s).lipschitz ?_).lipschitzOnWith
    exact hC s (hmemIoo s hs)
  have ht₀ : t₀ ∈ Set.Ioo a b := by
    constructor
    · have : min t t₀ ≤ t₀ := min_le_right _ _
      simp only [ha]; linarith
    · have : t₀ ≤ max t t₀ := le_max_right _ _
      simp only [hb]; linarith
  have htmem : t ∈ Set.Ioo a b := by
    constructor
    · have : min t t₀ ≤ t := min_le_left _ _
      simp only [ha]; linarith
    · have : t ≤ max t t₀ := le_max_left _ _
      simp only [hb]; linarith
  have key : Set.EqOn w (fun _ : ℝ => (0 : E)) (Set.Ioo a b) := by
    refine ODE_solution_unique_of_mem_Ioo (v := fun s x => A s x) (s := fun _ => Set.univ)
      hlip ht₀ (fun s _ => ⟨hw s, Set.mem_univ _⟩) (fun s _ => ⟨?_, Set.mem_univ _⟩) (by simp [h0])
    simpa using hasDerivAt_const s (0 : E)
  simpa using key htmem

/-- **Adiabatic theorem** (Kato's exact formulation).

`H t` is a (bounded, self-adjoint) time-dependent Hamiltonian on a complex Hilbert space `E`,
whose instantaneous, *nondegenerate* eigenvalue `Ev t` has the one-dimensional eigenspace
spanned by the unit vector `e t`; `P t v = ⟪e t, v⟫ • e t` is the corresponding rank-one
spectral projection, and `P' t` is its derivative.

The state `psi` evolves under the adiabatic (slow) dynamics with slowness parameter `ε > 0`:
`ε ψ'(t) = -i H(t) ψ(t) + ε [P'(t), P(t)] ψ(t)`, i.e. the Schrödinger equation on the slow
time scale, corrected by Kato's geometric term `[P' t, P t] = P' t P t - P t P' t`, which is
exactly the generator obtained in the adiabatic limit of a slowly varying Hamiltonian.

Conclusion: a state started in the eigenstate `e 0` stays, for all times, inside the
instantaneous eigenspace: `psi t` is fixed by `P t`, it is an instantaneous eigenvector of
`H t` for the instantaneous eigenvalue `Ev t`, and it remains a multiple of `e t`. -/
