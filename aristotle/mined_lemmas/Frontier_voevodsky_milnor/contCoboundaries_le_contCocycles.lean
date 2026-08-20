import Mathlib

/-!
# Voevodsky Milnor: definitions and supporting results

Supporting development for `Frontier.voevodsky_milnor` (see `RequestProject/Main.lean`):
mod-2 Milnor K-theory, mod-2 Galois cohomology, the statement of the Milnor conjecture, the
degree-zero base case, the separably closed case, and the degree-one identifications.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false

namespace Frontier

/-!
## Mod-2 Milnor K-theory

For a field `F`, the `n`-th Milnor K-group `K^M_n(F)` is the degree-`n` part of the quotient of
the tensor algebra of the abelian group `Fˣ` by the Steinberg relations `a ⊗ (1 - a) = 0`.
Reducing mod 2, `k^M_n(F) = K^M_n(F)/2` is therefore the quotient of the free `ZMod 2`-module on
`n`-tuples of units by
* multilinearity in each slot, and
* the Steinberg relations (in adjacent slots).

This is the definition used below.
-/

section Milnor

variable (F : Type) [Field F]

/-- The defining relations of mod-2 Milnor K-theory in degree `n`: multilinearity in each slot,
and the Steinberg relation `{a, 1 - a} = 0` in adjacent slots. -/

lemma contCoboundaries_le_contCocycles (n : ℕ) :
    contCoboundaries F n ≤ contCocycles F n := by
  cases n with
  | zero => simp [contCoboundaries]
  | succ m =>
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨dd_mem_contCochains F hf, dd_dd (AbsGal F) m f⟩

/-- Mod-2 Galois cohomology `H^n(F, ℤ/2)`: continuous cochain cohomology of the absolute Galois
group of `F` with trivial `ℤ/2` coefficients. -/
abbrev GaloisCohomologyMod2 (n : ℕ) : Type :=
  contCocycles F n ⧸ Submodule.comap (contCocycles F n).subtype (contCoboundaries F n)

end GaloisCohomology

/-!
## The statement of the Milnor conjecture
-/

/-- The Milnor conjecture (Voevodsky's theorem) in degree `n` for the field `F`: mod-2 Milnor
K-theory in degree `n` agrees with mod-2 Galois cohomology in degree `n`.

(The full theorem asserts moreover that the comparison is induced by the norm-residue / Galois
symbol map; here we only record the existence of an isomorphism of `ℤ/2`-vector spaces.) -/
