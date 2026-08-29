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

import Mathlib
import RequestProject.H10.Factorial

/-!
# The product `∏_{k=1}^{y} (a + b*k)` is Diophantine

This is the last of the classical auxiliary Diophantine functions needed for the
Davis–Putnam–Robinson elimination of bounded universal quantifiers.

The idea is that modulo a large `N` coprime to `b`, one has
`∏_{k=1}^{y} (a + b k) ≡ b^y ∏_{k=1}^{y} (m + k) = b^y y! binom(m+y, y)`
where `m` is the residue `a * b⁻¹ mod N`.
-/

namespace H10

open Nat Finset Dioph

/-- `prodAB a b y = (a + b) * (a + 2b) * ⋯ * (a + y b)`. -/

theorem prod_dvd_of_pairwise_coprime {ι : Type} {s : Finset ι} {f : ι → ℕ} {z : ℕ}
    (hco : (s : Set ι).Pairwise (Function.onFun Nat.Coprime f))
    (h : ∀ i ∈ s, f i ∣ z) : (∏ i ∈ s, f i) ∣ z := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hco' : (s : Set ι).Pairwise (Function.onFun Nat.Coprime f) :=
        hco.mono (by simp [Finset.coe_insert, Set.subset_insert])
      have hcop : Nat.Coprime (f a) (∏ i ∈ s, f i) := by
        apply Nat.Coprime.prod_right
        intro i hi
        exact hco (by simp) (by simp [hi]) (by rintro rfl; exact ha hi)
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (h a (by simp))
        (ih hco' (fun i hi => h i (by simp [hi])))

/-- Soundness of the Davis–Putnam–Robinson coding: the arithmetic conditions imply that
every `k < N` has a witness. -/
