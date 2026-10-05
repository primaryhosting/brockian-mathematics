import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-! ## The two–dimensional XY model -/

/-- Sites of the two-dimensional square lattice `ℤ²`. -/
abbrev Site : Type := ℤ × ℤ

/-- The XY-model Hamiltonian `H(θ) = -J ∑_{⟨xy⟩} cos (θ x - θ y)` for a finite collection
of nearest-neighbour bonds. -/

theorem vorticity_quantized (θ : Site → ℝ) (p : Fin 4 → Site) :
    ∃ k : ℤ, vorticity θ p = 2 * Real.pi * k := by
  have hsum : ∑ i : Fin 4, (θ (p (i + 1)) - θ (p i)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have : ∑ i : Fin 4, θ (p (i + 1)) = ∑ i : Fin 4, θ (p i) :=
      Fintype.sum_equiv (Equiv.addRight (1 : Fin 4)) _ _ (fun i => rfl)
    rw [this, sub_self]
  have hcoe : ((vorticity θ p : ℝ) : Real.Angle) = 0 := by
    have hs : ((vorticity θ p : ℝ) : Real.Angle)
        = ∑ i : Fin 4, ((wrap (θ (p (i + 1)) - θ (p i)) : ℝ) : Real.Angle) := by
      rw [vorticity]; rfl
    rw [hs]
    have h2 : ∀ i : Fin 4, ((wrap (θ (p (i + 1)) - θ (p i)) : ℝ) : Real.Angle)
        = ((θ (p (i + 1)) - θ (p i) : ℝ) : Real.Angle) := by
      intro i
      simp [wrap, Real.Angle.coe_toReal]
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    have : ∑ i : Fin 4, ((θ (p (i + 1)) - θ (p i) : ℝ) : Real.Angle)
        = ((∑ i : Fin 4, (θ (p (i + 1)) - θ (p i)) : ℝ) : Real.Angle) :=
      (map_sum Real.Angle.coeHom _ Finset.univ).symm
    rw [this, hsum]
    simp
  obtain ⟨n, hn⟩ := Real.Angle.coe_eq_zero_iff.mp hcoe
  exact ⟨n, by rw [← hn]; simp [zsmul_eq_mul]; ring⟩

/-! ## Energy and entropy of an isolated vortex -/

/-- The (spin-wave) energy of a single unit vortex in a box of linear size `L`, measured in
units of the lattice spacing: the energy density is `(J/2)|∇θ|²` with `|∇θ| = 1/r`, so that
integrating over the annulus `1 ≤ r ≤ L` gives `∫ (J/2) r⁻² · 2π r dr`. -/
