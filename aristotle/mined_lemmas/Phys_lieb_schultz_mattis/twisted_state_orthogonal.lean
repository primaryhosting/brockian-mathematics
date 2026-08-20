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

theorem twisted_state_orthogonal
    (T U : V →ₗ[ℂ] V) (ψ : V) (c : ℂ)
    (hTiso : ∀ x y : V, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hTU : ∀ x : V, T (U x) = -(U (T x)))
    (hTψ : T ψ = c • ψ) (hc : ‖c‖ = 1) :
    ⟪ψ, U ψ⟫_ℂ = 0 := by
  have key : ⟪ψ, U ψ⟫_ℂ = -⟪ψ, U ψ⟫_ℂ := by
    have h1 : ⟪T ψ, T (U ψ)⟫_ℂ = ⟪ψ, U ψ⟫_ℂ := hTiso ψ (U ψ)
    have h2 : T (U ψ) = -(c • U ψ) := by
      rw [hTU ψ, hTψ, map_smul]
    rw [h2, hTψ, inner_smul_left, inner_neg_right, inner_smul_right] at h1
    have hcc : (starRingEnd ℂ) c * c = 1 := by
      rw [RCLike.conj_mul (K := ℂ) c, hc]
      norm_num
    calc ⟪ψ, U ψ⟫_ℂ = (starRingEnd ℂ) c * -(c * ⟪ψ, U ψ⟫_ℂ) := h1.symm
      _ = -(((starRingEnd ℂ) c * c) * ⟪ψ, U ψ⟫_ℂ) := by ring
      _ = -⟪ψ, U ψ⟫_ℂ := by rw [hcc]; ring
  have : (2 : ℂ) * ⟪ψ, U ψ⟫_ℂ = 0 := by linear_combination key
  simpa using this

/-- **Lieb–Schultz–Mattis theorem (abstract form): a half-integer-spin translation-invariant
chain is gapless or degenerate.**

Data:
* `V` — the (complex) Hilbert space of states of the chain;
* `H` — the Hamiltonian, translation invariant (`hHT`);
* `T` — the lattice translation, an isometry (`hTiso`);
* `U` — the Lieb–Schultz–Mattis twist operator, an isometry (`hUiso`), which *anticommutes*
  with the translation (`hTU`).  This anticommutation is exactly the statement that the twist
  shifts the momentum by `π`, which is what a half-odd-integer spin per unit cell produces;
* `ψ` — a normalized ground state of energy `E₀`;
* `htwist` — the variational bound saying that the twisted state has energy at most `E₀ + ε`
  (for the physical chain of length `L`, `ε = O(1/L)`).

Conclusion (the LSM alternative): either the ground state is **degenerate** — there is another
ground state of the same energy `E₀`, orthogonal to `ψ` — or the system is **gapless** in the
sense that every candidate gap `Δ` below the excited spectrum obeys `Δ ≤ ε`. -/
