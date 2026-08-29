import Mathlib

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

import RequestProject.AKS.Defs

/-!
# Introspective exponents

Fix a prime `p` and let `F = AlgebraicClosure (ZMod p)`.  A natural number `m` is
*introspective* for a polynomial `f ∈ 𝔽ₚ[X]` (relative to `r`) if `f(z)^m = f(z^m)` for every
`r`-th root of unity `z ∈ F`.  This is the key notion in the AKS correctness proof.
-/

open Polynomial

namespace CS
namespace AKS

/-- The algebraic closure of `𝔽ₚ`, the field in which the AKS argument takes place. -/
abbrev AC (p : ℕ) [Fact p.Prime] := AlgebraicClosure (ZMod p)

variable {p : ℕ} [Fact p.Prime]

/-- `m` is introspective for `f`: `f(z)^m = f(z^m)` for all `r`-th roots of unity `z`. -/

lemma poly_eq_of_many_roots {f g : (ZMod p)[X]} {L : ℕ} (hf : f.natDegree ≤ L)
    (hg : g.natDegree ≤ L) (W : Finset (AC p)) (hW : L < W.card)
    (h : ∀ w ∈ W, aeval w f = aeval w g) : f = g := by
  classical
  by_contra hne
  have hfg : f - g ≠ 0 := sub_ne_zero.mpr hne
  set D : (AC p)[X] := (f - g).map (algebraMap (ZMod p) (AC p)) with hD
  have hD0 : D ≠ 0 := by
    rw [hD, Polynomial.map_ne_zero_iff (algebraMap (ZMod p) (AC p)).injective]
    exact hfg
  have hDdeg : D.natDegree ≤ L := by
    rw [hD, natDegree_map_eq_of_injective (algebraMap (ZMod p) (AC p)).injective]
    exact le_trans (natDegree_sub_le f g) (max_le hf hg)
  have hsub : W.val ⊆ D.roots := by
    intro w hw
    have hw' : w ∈ W := Finset.mem_val.mp hw
    rw [mem_roots hD0]
    have : aeval w (f - g) = 0 := by
      rw [map_sub, h w hw', sub_self]
    simpa [hD, IsRoot.def, eval_map, ← aeval_def] using this
  have := card_le_degree_of_subset_roots hsub
  omega

/-- The products `∏_{a ∈ S} (X + a)` over subsets `S` of `[1, L]` are pairwise distinct,
provided `L < p`. -/
