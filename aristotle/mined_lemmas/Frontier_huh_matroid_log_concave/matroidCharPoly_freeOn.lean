/-
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Frontier

open Polynomial Finset

/-- The characteristic polynomial of a matroid `M` with finite ground set `E`, given by
Whitney's rank generating formula
`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`,
where `r` is the (natural-number valued) rank function of `M`. -/

theorem matroidCharPoly_freeOn {ι : Type*} (E : Finset ι) :
    matroidCharPoly (Matroid.freeOn (E : Set ι)) E = (X - 1) ^ E.card := by
  unfold matroidCharPoly
  have hE : ∀ S ∈ E.powerset,
      (-1 : Polynomial ℤ) ^ S.card *
          X ^ (((Matroid.freeOn (E : Set ι)).eRk (E : Set ι)).toNat -
            ((Matroid.freeOn (E : Set ι)).eRk (S : Set ι)).toNat)
        = (-1 : Polynomial ℤ) ^ S.card * X ^ (E.card - S.card) := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    rw [Matroid.eRk_freeOn (le_refl _), Matroid.eRk_freeOn (by exact_mod_cast hS),
      Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard]
    norm_num
  rw [Finset.sum_congr rfl hE,
    Finset.sum_powerset_apply_card (fun m => (-1 : Polynomial ℤ) ^ m * X ^ (E.card - m))]
  have hX : ((X : Polynomial ℤ) - 1) ^ E.card = ((-1 : Polynomial ℤ) + X) ^ E.card := by ring
  rw [hX, add_pow]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [nsmul_eq_mul]
  ring

/-- The absolute values of the coefficients of `(X - 1)^n` are the binomial coefficients. -/
