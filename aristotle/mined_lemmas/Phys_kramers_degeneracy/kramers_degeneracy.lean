/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
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

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A *time-reversal operator* on a complex inner product space: an antiunitary map `T`
(additive, conjugate-homogeneous, and inner-product reversing) which squares to `-1`.
The condition `T (T a) = -a` is exactly what holds for half-integer spin
(for integer spin one has `T² = +1`). -/
structure IsTimeReversal (T : V → V) : Prop where
  /-- `T` is additive. -/
  map_add : ∀ a b, T (a + b) = T a + T b
  /-- `T` is conjugate-homogeneous. -/
  map_smul : ∀ (c : ℂ) (a : V), T (c • a) = (starRingEnd ℂ) c • T a
  /-- `T` is antiunitary: it conjugates inner products. -/
  inner_map : ∀ a b, ⟪T a, T b⟫_ℂ = ⟪b, a⟫_ℂ
  /-- Half-integer spin: `T² = -1`. -/
  sq_eq_neg : ∀ a, T (T a) = -a

/-- For a half-integer-spin time reversal, `T x` is orthogonal to `x`. -/

theorem kramers_degeneracy [FiniteDimensional ℂ V] {T : V → V} (hT : IsTimeReversal T)
    {H : V →ₗ[ℂ] V} (hH : H.IsSymmetric) (hTH : ∀ a, T (H a) = H (T a)) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue H μ) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace H μ) := by
  obtain ⟨x, hx_mem, hx⟩ := hμ.exists_hasEigenvector
  have hμreal : (starRingEnd ℂ) μ = μ := hH.conj_eigenvalue_eq_self hμ
  have hxe : H x = μ • x := Module.End.mem_eigenspace_iff.mp hx_mem
  have hTx : H (T x) = μ • T x := by
    rw [← hTH x, hxe, hT.map_smul, hμreal]
  have hindep : LinearIndependent ℂ ![x, T x] := hT.linearIndependent hx
  set W := Module.End.eigenspace H μ with hW
  have hmem1 : x ∈ W := hx_mem
  have hmem2 : T x ∈ W := Module.End.mem_eigenspace_iff.mpr hTx
  have hsub : LinearIndependent ℂ ![(⟨x, hmem1⟩ : W), ⟨T x, hmem2⟩] := by
    apply LinearIndependent.of_comp W.subtype
    convert hindep using 1
    ext i
    fin_cases i <;> simp
  simpa using hsub.fintype_card_le_finrank

/-! ### A concrete spin-1/2 system, showing the hypotheses are satisfiable -/

/-- Time reversal for a single spin-1/2 particle, `T = -i σ_y K` on `ℂ²`. -/
