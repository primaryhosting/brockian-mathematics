import Mathlib
/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
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

set_option grind.warning false

/-!
## The cap set problem

We prove the Croot–Lev–Pach / Ellenberg–Gijswijt bound: a subset of `𝔽₃ⁿ` containing no
non-trivial three-term arithmetic progression has size `o(3ⁿ)`.
-/

namespace CapSet

open Finset

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Points of `𝔽₃ⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → ZMod 3

/-- Exponent vectors of reduced monomials (each exponent is `0`, `1` or `2`). -/
abbrev Exp (n : ℕ) := Fin n → Fin 3

/-- The monomial function `x ↦ ∏ i, x i ^ α i` on `𝔽₃ⁿ`. -/

lemma finrank_inf_ker_ge {V W : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] [AddCommGroup W] [Module (ZMod 3) W]
    [FiniteDimensional (ZMod 3) W] (S : Submodule (ZMod 3) V) (f : V →ₗ[ZMod 3] W) :
    Module.finrank (ZMod 3) S ≤
      Module.finrank (ZMod 3) (S ⊓ LinearMap.ker f : Submodule (ZMod 3) V)
        + Module.finrank (ZMod 3) W := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict S)
  have h1 : Module.finrank (ZMod 3) (LinearMap.range (f.domRestrict S))
      ≤ Module.finrank (ZMod 3) W := Submodule.finrank_le _
  have h2 : Module.finrank (ZMod 3) (LinearMap.ker (f.domRestrict S))
      = Module.finrank (ZMod 3) (S ⊓ LinearMap.ker f : Submodule (ZMod 3) V) := by
    rw [LinearMap.ker_domRestrict,
      ← Submodule.finrank_map_subtype_eq S (Submodule.comap S.subtype (LinearMap.ker f)),
      Submodule.map_comap_subtype]
  omega

/-- The Croot–Lev–Pach / Ellenberg–Gijswijt bound. -/
