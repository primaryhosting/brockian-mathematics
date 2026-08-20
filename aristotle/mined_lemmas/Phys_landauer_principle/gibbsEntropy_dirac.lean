import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Statement: Erasing one bit dissipates at least kT ln 2 of heat (Landauer).
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

/-- The Gibbs (Boltzmann–Shannon) entropy `S = -k ∑ᵢ pᵢ log pᵢ` of a probability
distribution `p` on a finite set of microstates, with Boltzmann constant `k`. -/

theorem gibbsEntropy_dirac {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℝ) (i₀ : ι)
    (p : ι → ℝ) (hp : ∀ i, p i = if i = i₀ then 1 else 0) :
    gibbsEntropy k p = 0 := by
  have h : ∀ i : ι,
      (if i = i₀ then (1 : ℝ) else 0) * Real.log (if i = i₀ then (1 : ℝ) else 0) = 0 := by
    intro i
    by_cases hi : i = i₀ <;> simp [hi]
  simp only [gibbsEntropy, hp, h]
  simp

/--
**Landauer's principle.**

A memory bit is modelled as a two-state system (`Bool`) with Boltzmann constant `k`,
in contact with a heat bath at temperature `T > 0`.  Initially the bit is unknown, i.e.
its distribution `pInit` is uniform; after the erasure operation the bit is in a definite
state `b₀`, i.e. the distribution `pFinal` is the point mass at `b₀`.

The only physical input is the second law of thermodynamics in the form
`ΔS_total = ΔS_system + Q/T ≥ 0`, where `Q` is the heat dissipated into the bath.

Conclusion: the dissipated heat satisfies `Q ≥ k T log 2`, i.e. at least `kT ln 2`
of heat is released when one bit of information is erased.
-/
