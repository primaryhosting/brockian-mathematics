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


theorem emb_ppow (n r : ℕ) (hr : 0 < r) (base : List ℕ) (e : ℕ) :
    Cong r (emb n r (ppow n r base e)) ((emb n r base) ^ e) := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
      match e with
      | 0 => rw [ppow, emb_pone n r hr]; simpa using Cong.refl r 1
      | (m + 1) =>
          have hhalf : (m + 1) / 2 < m + 1 := by omega
          have ihh := ih ((m + 1) / 2) hhalf
          rw [ppow]
          have hsq : Cong r (emb n r (pmul n r (ppow n r base ((m + 1) / 2))
              (ppow n r base ((m + 1) / 2))))
              ((emb n r base) ^ ((m + 1) / 2 * 2)) := by
            refine (emb_pmul n r hr _ _).trans ?_
            have := ihh.mul ihh
            refine this.trans ?_
            rw [← pow_add]
            have : (m + 1) / 2 + (m + 1) / 2 = (m + 1) / 2 * 2 := by ring
            rw [this]
            exact Cong.refl r _
          split
          · rename_i heven
            have : (m + 1) / 2 * 2 = m + 1 := by omega
            rw [this] at hsq
            exact hsq
          · rename_i hodd
            refine (emb_pmul n r hr _ _).trans ?_
            refine (hsq.mul (Cong.refl r (emb n r base))).trans ?_
            rw [← pow_succ]
            have hexp : (m + 1) / 2 * 2 + 1 = m + 1 := by omega
            rw [hexp]
            exact Cong.refl r _

