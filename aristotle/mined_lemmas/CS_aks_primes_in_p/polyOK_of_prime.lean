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


theorem polyOK_of_prime {n : ℕ} [Fact n.Prime] {r : ℕ} (hr : 0 < r) (a : ℕ) :
    polyOK n r a = true := by
  have hn : 1 < n := (Fact.out (p := n.Prime)).one_lt
  haveI : CharP (ZMod n) n := ZMod.charP n
  have hfrob : ((X : (ZMod n)[X]) + C ((a : ℕ) : ZMod n)) ^ n
      = X ^ n + C ((a : ℕ) : ZMod n) := by
    rw [add_pow_char]
    congr 1
    rw [← map_pow, ZMod.pow_card]
  rw [polyOK, beq_iff_eq]
  refine emb_injective n r hr (length_ppow n r _ n) (length_pXAdd n r n a)
    (fun k hk => getD_ppow_lt n r hn _ n k hk) (fun k hk => getD_pXAdd_lt n r n a (by omega) k hk)
    ?_
  have h1 : Cong r (emb n r (ppow n r (pXAdd n r 1 a) n))
      (((X : (ZMod n)[X]) + C ((a : ℕ) : ZMod n)) ^ n) := by
    refine (emb_ppow n r hr _ n).trans ?_
    refine Cong.pow ?_ n
    have := emb_pXAdd n r 1 a hr
    simpa using this
  have h2 : Cong r (emb n r (pXAdd n r n a))
      ((X : (ZMod n)[X]) ^ n + C ((a : ℕ) : ZMod n)) := emb_pXAdd n r n a hr
  rw [hfrob] at h1
  exact h1.trans h2.symm

/-- If every `a` in `[2, r]` has `gcd a n ∈ {1, n}` and `n ≤ r`, then `n` is prime. -/
