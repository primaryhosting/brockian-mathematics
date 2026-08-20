/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
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

open ComplexConjugate

section LSM

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Momentum obstruction (core of the Lieb–Schultz–Mattis argument).**

If the translation operator `T` is an isometry, the twist operator `U` anticommutes with `T`
(this is the algebraic footprint of a *half-integer* spin per unit cell: the twist shifts the
momentum by `π`), and `ψ` is a translation eigenvector, then the twisted state `U ψ` is
orthogonal to `ψ`. -/

theorem lieb_schultz_mattis_no_unique_gapped_ground_state
    (H T U : V →ₗ[ℂ] V) (ψ : V) (E₀ ε Δ : ℝ)
    (hTiso : ∀ x y : V, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hUiso : ∀ x y : V, ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hHT : ∀ x : V, H (T x) = T (H x))
    (hTU : ∀ x : V, T (U x) = -(U (T x)))
    (hψ : ‖ψ‖ = 1)
    (hgs : H ψ = (E₀ : ℂ) • ψ)
    (htwist : (⟪U ψ, H (U ψ)⟫_ℂ).re ≤ E₀ + ε)
    (hgap : ∀ v : V, ‖v‖ = 1 → ⟪ψ, v⟫_ℂ = 0 → E₀ + Δ ≤ (⟪v, H v⟫_ℂ).re)
    (hΔ : ε < Δ)
    (huniq : ∀ v : V, H v = (E₀ : ℂ) • v → ∃ c : ℂ, v = c • ψ) :
    False := by
  rcases lieb_schultz_mattis H T U ψ E₀ ε Δ hTiso hUiso hHT hTU hψ hgs htwist hgap with
    ⟨v, hv1, hv2, hv3⟩ | hle
  · obtain ⟨c, rfl⟩ := huniq v hv3
    have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
    rw [inner_smul_right, hψψ, mul_one] at hv2
    rw [hv2, zero_smul, norm_zero] at hv1
    exact zero_ne_one hv1
  · linarith

end LSM

section Example

/-! ### The hypotheses are not vacuous

A two-level example (a single half-integer spin): the "translation" is the Pauli matrix `σ_z`,
the twist operator is `σ_x` (these anticommute, which is the half-integer-spin input of LSM),
and the Hamiltonian is `diag (0, 1)`.  Here the ground state has energy `0`, the gap equals `1`,
and the twisted state indeed has energy `1 = E₀ + ε` with `ε = 1`. -/

/-- The "translation" operator of the two-level example: the Pauli matrix `σ_z`. -/
