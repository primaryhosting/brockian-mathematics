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

lemma finrank_polySpace (n d : ℕ) :
    Module.finrank (ZMod 3) (polySpace n d) = mcount n d := by
  have hli : LinearIndependent (ZMod 3) (fun α : {x // x ∈ Dset n d} => mono (α : Exp n)) :=
    (mono_linearIndependent n).comp _ Subtype.val_injective
  have hrange : Set.range (fun α : {x // x ∈ Dset n d} => mono (α : Exp n))
      = mono '' (Dset n d : Set (Exp n)) := by
    ext p
    simp [Set.mem_range, Set.mem_image]
  have h := finrank_span_eq_card hli
  rw [hrange] at h
  rw [polySpace, h, mcount, Fintype.card_coe]

/-! ### A subspace of functions contains a function with large support -/

