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

lemma rotZ_rotX_anticomm {n : ℕ} (hn : Odd n) :
    rotZ n ∘ₗ rotX n = (-1 : ℂ) • (rotX n ∘ₗ rotZ n) := by
  ext f s
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [rotZ_apply, rotX_apply, rotX_apply, rotZ_apply, sgn_flip, hn.neg_one_pow]
  ring

/-! ## Lieb–Schultz–Mattis -/

/-- **Lieb–Schultz–Mattis.**  Consider a chain of an odd number `n` of half-integer
(spin-1/2) sites, with a Hamiltonian `H` that is translation invariant and invariant
under the global spin rotations by `π` about the `x`- and `z`-axes.  Then the system
cannot have a unique gapped ground state: *every* energy level of `H` — in particular
the ground level — is degenerate, its eigenspace having dimension at least `2`.
(Equivalently: the gap above any eigenstate vanishes, so the chain is gapless or
degenerate.)

The translation invariance hypothesis `hHT` is the one demanded by the physical
statement; the proof shows it is not needed once the number of half-integer spins is
odd. -/
