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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-! ## The abstract mechanism: an anomalous (projective) commutation relation
forces every energy level to be degenerate. -/

/-- **Anomaly ⇒ degeneracy.**  If a Hamiltonian `H` commutes with two injective
symmetries `A` and `B` which fail to commute with each other by a phase `ω ≠ 1`
(`B ∘ A = ω • (A ∘ B)`), then no eigenvector of `H` spans its own eigenspace:
each eigenspace of `H` has dimension at least `2`. -/

theorem anomalous_symmetries_degenerate
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H A B : V →ₗ[ℂ] V) (ω : ℂ) (hω : ω ≠ 1)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hHA : H ∘ₗ A = A ∘ₗ H) (hHB : H ∘ₗ B = B ∘ₗ H)
    (hanom : B ∘ₗ A = ω • (A ∘ₗ B))
    (E : ℂ) (hE : Module.End.HasEigenvalue H E) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace H E) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨v, hvmem, hv0⟩ := hE.exists_hasEigenvector
  have hHv : H v = E • v := Module.End.mem_eigenspace_iff.mp hvmem
  have hspan : (ℂ ∙ v) ≤ Module.End.eigenspace H E :=
    (Submodule.span_singleton_le_iff_mem _ _).2 hvmem
  have h1 : Module.finrank ℂ (ℂ ∙ v) = 1 := finrank_span_singleton hv0
  have heq : (ℂ ∙ v) = Module.End.eigenspace H E := by
    refine Submodule.eq_of_le_of_finrank_le hspan ?_
    omega
  have hAmem : A v ∈ Module.End.eigenspace H E := by
    refine Module.End.mem_eigenspace_iff.mpr ?_
    have := LinearMap.congr_fun hHA v
    simp only [LinearMap.comp_apply] at this
    rw [this, hHv, map_smul]
  have hBmem : B v ∈ Module.End.eigenspace H E := by
    refine Module.End.mem_eigenspace_iff.mpr ?_
    have := LinearMap.congr_fun hHB v
    simp only [LinearMap.comp_apply] at this
    rw [this, hHv, map_smul]
  rw [← heq, Submodule.mem_span_singleton] at hAmem hBmem
  obtain ⟨a, ha⟩ := hAmem
  obtain ⟨b, hb⟩ := hBmem
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hv0
    apply hA
    rw [← ha]
    simp
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hv0
    apply hB
    rw [← hb]
    simp
  have hkey := LinearMap.congr_fun hanom v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hkey
  rw [← ha, ← hb] at hkey
  rw [map_smul, map_smul, ← hb, ← ha] at hkey
  rw [smul_smul, smul_smul, smul_smul] at hkey
  have hzero : (a * b - ω * b * a) • v = 0 := by
    rw [sub_smul, hkey, sub_self]
  rcases smul_eq_zero.mp hzero with h | h
  · have h' : a * b * (1 - ω) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact ha0 h3
      · exact hb0 h3
    · exact hω (sub_eq_zero.mp h2).symm
  · exact hv0 h

/-! ## A chain of an odd number of spin-1/2 (half-integer spin) sites -/

/-- Spin configurations of a chain of `n` sites, each carrying a spin-1/2. -/
abbrev Config (n : ℕ) := Fin n → Bool

/-- The Hilbert space of the chain: functions on configurations. -/
abbrev ChainSpace (n : ℕ) := Config n → ℂ

/-- Flipping every spin of the chain. -/
