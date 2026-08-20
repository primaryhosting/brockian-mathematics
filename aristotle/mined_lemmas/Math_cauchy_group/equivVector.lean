import Mathlib

/-!
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-!
## McKay's proof of Cauchy's theorem

The whole argument is developed from scratch here: we consider the set of lists of length `p`
of elements of `G` whose product is `1`, let the cyclic group `ZMod p` act on it by rotation,
and compare the cardinality of this set (which is `|G| ^ (p-1)`, divisible by `p`) with the
cardinality of the set of fixed points (constant lists `[g, …, g]` with `g ^ p = 1`) modulo `p`.
-/

/-- The set of lists of length `p` of elements of `G` whose product is `1`. -/

def equivVector (hp : 0 < p) : ProdOne G p ≃ List.Vector G (p - 1) where
  toFun x := ⟨x.1.dropLast, by
    rw [List.length_dropLast, x.2.1]⟩
  invFun w := ⟨w.1 ++ [w.1.prod⁻¹], by
    refine ⟨?_, ?_⟩
    · simp only [List.length_append, w.2, List.length_singleton]
      omega
    · simp⟩
  left_inv x := by
    apply ext
    have hne : x.1 ≠ [] := by
      intro h
      have hl := x.2.1
      rw [h, List.length_nil] at hl
      omega
    show x.1.dropLast ++ [x.1.dropLast.prod⁻¹] = x.1
    obtain ⟨d, a, hd⟩ : ∃ d a, x.1 = d ++ [a] :=
      ⟨x.1.dropLast, x.1.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    have hprod : d.prod * a = 1 := by
      have h2 := x.2.2
      rw [hd, List.prod_append] at h2
      simpa using h2
    rw [hd, List.dropLast_concat, eq_inv_of_mul_eq_one_left hprod, inv_inv]
  right_inv w := by
    apply Subtype.ext
    show (w.1 ++ [w.1.prod⁻¹]).dropLast = w.1
    exact List.dropLast_concat

