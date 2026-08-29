import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file header: Lean 4 requires `import` commands to be the very first
commands of a module, so the required header block is placed immediately after
the single `import Mathlib` line.
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

set_option grind.warning false

namespace Phys

/-!
## Setting

We formalise the algebraic (Lieb–Schultz–Mattis / Oshikawa–Yamanaka–Affleck) mechanism
that forbids a non-degenerate energy level in a translation invariant spin chain whose
spin per unit cell is a half-odd-integer.

A finite chain is described by:

* a complex vector space `V` (the Hilbert space of the ring of `L` sites),
* the Hamiltonian `H : V →ₗ[ℂ] V`,
* the (invertible) lattice translation `T`,
* the (invertible) `U(1)` twist operator `U = exp (2πi/L · Σⱼ j Sᶻⱼ)` used in the
  flux-insertion argument,
* the spin per unit cell `spin`, assumed to be a half-odd-integer.

The two physical inputs are:

* `H` commutes with `T` (translation invariance) and with `U` (the twist is built from
  a conserved charge, so it commutes with the Hamiltonian);
* the *LSM commutation relation* `T U = e^{2πi·spin} U T`, i.e. conjugating the twist
  operator by a translation produces the anomalous phase `e^{2πi·spin}`, which equals
  `-1` exactly when the spin per unit cell is a half-odd-integer.

The conclusion is that **no** energy level of `H` is simple: every eigenvalue has at
least a two-dimensional eigenspace.  In particular the ground state is degenerate, so
the chain is gapless or degenerate.
-/

/-- Data of a translation invariant spin chain carrying a half-odd-integer spin per unit
cell, together with the twist operator entering the Lieb–Schultz–Mattis flux argument. -/
structure HalfIntegerSpinChain (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- The Hamiltonian. -/
  H : V →ₗ[ℂ] V
  /-- The lattice translation operator (invertible). -/
  T : V ≃ₗ[ℂ] V
  /-- The `U(1)` twist ("flux insertion") operator (invertible). -/
  U : V ≃ₗ[ℂ] V
  /-- The spin per unit cell. -/
  spin : ℚ
  /-- The spin per unit cell is a half-odd-integer. -/
  spin_half_integer : ∃ k : ℤ, spin = (k : ℚ) + 1 / 2
  /-- Translation invariance of the Hamiltonian. -/
  translation_invariant : ∀ v : V, H (T v) = T (H v)
  /-- The twist operator is a symmetry of the Hamiltonian. -/
  symmetry_invariant : ∀ v : V, H (U v) = U (H v)
  /-- The Lieb–Schultz–Mattis commutation relation: translating the twist operator
  produces the phase `e^{2πi·spin}`. -/
  lsm_relation :
    ∀ v : V, T (U v) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (spin : ℂ)) • U (T v)

/-- An eigenvalue `E` of `H` is *degenerate* when its eigenspace contains two linearly
independent vectors. -/

theorem lieb_schultz_mattis_nonvacuous : Nonempty (HalfIntegerSpinChain (Fin 2 → ℂ)) :=
  ⟨spinHalfExample⟩

end Phys

