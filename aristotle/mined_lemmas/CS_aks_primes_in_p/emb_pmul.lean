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

import RequestProject.AKS.Algorithm

/-!
# Correctness of the AKS primality test

The main result of this file is `AKS.aksTest_iff_prime`:
the decision procedure `AKS.aksTest` returns `true` exactly on the primes.
-/

namespace AKS

open Polynomial Finset


theorem emb_pmul (n r : ℕ) (hr : 0 < r) (f g : List ℕ) :
    Cong r (emb n r (pmul n r f g)) (emb n r f * emb n r g) := by
  classical
  set F : ℕ → ZMod n := fun i => ((f.getD i 0 : ℕ) : ZMod n) with hF
  set G : ℕ → ZMod n := fun i => ((g.getD i 0 : ℕ) : ZMod n) with hG
  -- the product, expanded
  have hprod : emb n r f * emb n r g =
      ∑ q ∈ Finset.range r ×ˢ Finset.range r, C (F q.1 * G q.2) * X ^ (q.1 + q.2) := by
    rw [emb, emb, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  -- reduce the exponents modulo r
  have hstep : Cong r (∑ q ∈ Finset.range r ×ˢ Finset.range r,
      C (F q.1 * G q.2) * X ^ ((q.1 + q.2) % r))
      (∑ q ∈ Finset.range r ×ˢ Finset.range r, C (F q.1 * G q.2) * X ^ (q.1 + q.2)) := by
    refine Cong.sum _ fun q _ => ?_
    exact (Cong.refl r _).mul (cong_X_pow_mod r (q.1 + q.2) hr).symm
  -- group by the residue
  have hgroup : ∑ q ∈ Finset.range r ×ˢ Finset.range r,
      C (F q.1 * G q.2) * X ^ ((q.1 + q.2) % r) =
      ∑ k ∈ Finset.range r, (∑ q ∈ (Finset.range r ×ˢ Finset.range r) with (q.1 + q.2) % r = k,
        C (F q.1 * G q.2)) * X ^ k := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (t := Finset.range r) (g := fun q : ℕ × ℕ => (q.1 + q.2) % r)
      (fun q _ => Finset.mem_range.2 (Nat.mod_lt _ hr))
      (fun q => C (F q.1 * G q.2) * X ^ ((q.1 + q.2) % r))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [(Finset.mem_filter.1 hq).2]
  -- the left-hand side
  have hlhs : emb n r (pmul n r f g) =
      ∑ k ∈ Finset.range r, (∑ q ∈ (Finset.range r ×ˢ Finset.range r) with (q.1 + q.2) % r = k,
        C (F q.1 * G q.2)) * X ^ k := by
    rw [emb]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < r := Finset.mem_range.1 hk
    rw [pmul, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk']
    simp only [Option.map_some, Option.getD_some, ZMod.natCast_mod]
    rw [Nat.cast_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    push_cast
    rw [map_mul]
  rw [hlhs, ← hgroup, hprod]
  exact hstep

