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

theorem ext {x y : ProdOne G p} (h : x.1 = y.1) : x = y := Subtype.ext h

instance [Finite G] : Finite (ProdOne G p) := by
  cases nonempty_fintype G
  haveI : Finite (List.Vector G p) := inferInstance
  refine Finite.of_injective (β := List.Vector G p)
    (fun x : ProdOne G p => (⟨x.1, x.2.1⟩ : List.Vector G p)) ?_
  intro x y hxy
  exact ext (congrArg (fun v : List.Vector G p => v.1) hxy)

/-- Rotation gives an action of the cyclic group `Multiplicative (ZMod p)` on `ProdOne G p`. -/
instance instMulAction [NeZero p] :
    MulAction (Multiplicative (ZMod p)) (ProdOne G p) where
  smul k x :=
    ⟨x.1.rotate (Multiplicative.toAdd k).val,
      ⟨by rw [List.length_rotate, x.2.1], List.prod_rotate_eq_one_of_prod_eq_one x.2.2 _⟩⟩
  one_smul x := by
    apply ext
    show x.1.rotate (ZMod.val (0 : ZMod p)) = x.1
    simp
  mul_smul k l x := by
    apply ext
    have hlen : x.1.length = p := x.2.1
    have hmod : ∀ m : ℕ, x.1.rotate (m % p) = x.1.rotate m := by
      intro m
      have h := List.rotate_mod x.1 m
      rwa [hlen] at h
    show x.1.rotate ((Multiplicative.toAdd k + Multiplicative.toAdd l)).val
      = (x.1.rotate (Multiplicative.toAdd l).val).rotate (Multiplicative.toAdd k).val
    rw [List.rotate_rotate, ZMod.val_add, hmod, Nat.add_comm]

