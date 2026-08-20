import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## The Wigner–Eckart theorem

Physical setting.  A symmetry algebra (the group algebra of the symmetry group, or the universal
enveloping algebra of its Lie algebra — here an arbitrary `𝕜`-algebra `A`) acts on

* `X`  — the space of *product states* `|k q⟩ ⊗ |j m⟩` (tensor operator component ⊗ initial state),
* `W`  — the final irreducible multiplet `{|j' m'⟩}`, an irreducible (`IsSimpleModule A W`)
  finite-dimensional representation.

An *irreducible tensor operator* is, by definition, an equivariant (`A`-linear) map
`T : X →ₗ[A] W`, and its matrix elements are `⟨j' m'| T |k q; j m⟩ = bra m' (T (ket q m))`.
The *Clebsch–Gordan map* `C : X →ₗ[A] W` is a fixed nonzero equivariant map; its matrix elements
`bra m' (C (ket q m))` are the Clebsch–Gordan coefficients.

The one representation-theoretic input beyond irreducibility is *multiplicity freeness* of the
Clebsch–Gordan series: the final multiplet occurs exactly once in `X`.  This is encoded by
a decomposition `X = V ⊕ N` (`IsCompl V N`) into `A`-submodules where `V` is irreducible (the
unique copy of the final multiplet) and no copy of `W` survives in the complement `N`
(`hN : every A-linear map N → W vanishes`).

Conclusion: the matrix elements factor as
`⟨j' m'| T |k q; j m⟩ = (Clebsch–Gordan coefficient) * r`,
with a single *reduced matrix element* `r` independent of `q`, `m`, `m'`.
-/

namespace Phys

section

variable {𝕜 A W : Type*} [Field 𝕜] [IsAlgClosed 𝕜] [Ring A] [Algebra 𝕜 A]
  [AddCommGroup W] [Module 𝕜 W] [Module A W] [IsScalarTower 𝕜 A W]
  [FiniteDimensional 𝕜 W] [IsSimpleModule A W]

/-- **Schur's lemma, scalar form.** Every equivariant endomorphism of a finite-dimensional
irreducible representation over an algebraically closed field is a scalar. -/

def Y₂ := ℂ

noncomputable instance : AddCommGroup W₂ := inferInstanceAs (AddCommGroup ℂ)
noncomputable instance : Module ℂ W₂ := inferInstanceAs (Module ℂ ℂ)
noncomputable instance : Module A₂ W₂ := Module.compHom ℂ (RingHom.fst ℂ ℂ)
noncomputable instance : AddCommGroup Y₂ := inferInstanceAs (AddCommGroup ℂ)
noncomputable instance : Module ℂ Y₂ := inferInstanceAs (Module ℂ ℂ)
noncomputable instance : Module A₂ Y₂ := Module.compHom ℂ (RingHom.snd ℂ ℂ)

