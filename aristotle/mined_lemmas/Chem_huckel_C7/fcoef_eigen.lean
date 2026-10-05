/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Chem

open Finset Complex

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- A primitive 7-th root of unity. -/

lemma fcoef_eigen (μ : ℂ) (v : ZMod 7 → ℂ) (hAv : C7adj.mulVec v = μ • v) (k : ZMod 7) :
    μ * fcoef v k = lam7 k * fcoef v k := by
  have h1 : μ * fcoef v k = ∑ l : ZMod 7, (v (l - 1) + v (l + 1)) * chi7 (-(l * k)) := by
    rw [fcoef, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hl := congrFun hAv l
    rw [mulVec_C7adj] at hl
    simp only [Pi.smul_apply, smul_eq_mul] at hl
    rw [hl]
    ring
  have h2 : ∑ l : ZMod 7, v (l - 1) * chi7 (-(l * k)) = fcoef v k * chi7 (-k) := by
    have e2 : ∑ l : ZMod 7, v (l - 1) * chi7 (-(l * k))
        = ∑ l : ZMod 7, v l * chi7 (-((l + 1) * k)) := by
      refine Fintype.sum_equiv (Equiv.subRight (1 : ZMod 7)) _ _ (fun l => ?_)
      simp only [Equiv.subRight_apply, sub_add_cancel]
    rw [e2, fcoef, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hkk : -((l + 1) * k) = -(l * k) + (-k) := by ring
    rw [hkk, chi7_add]
    ring
  have h3 : ∑ l : ZMod 7, v (l + 1) * chi7 (-(l * k)) = fcoef v k * chi7 k := by
    have e3 : ∑ l : ZMod 7, v (l + 1) * chi7 (-(l * k))
        = ∑ l : ZMod 7, v l * chi7 (-((l - 1) * k)) := by
      refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod 7)) _ _ (fun l => ?_)
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [e3, fcoef, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hkk : -((l - 1) * k) = -(l * k) + k := by ring
    rw [hkk, chi7_add]
    ring
  have h4 : ∑ l : ZMod 7, (v (l - 1) + v (l + 1)) * chi7 (-(l * k))
      = (∑ l : ZMod 7, v (l - 1) * chi7 (-(l * k)))
        + ∑ l : ZMod 7, v (l + 1) * chi7 (-(l * k)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [h1, h4, h2, h3, ← chi7_add_chi7_neg k]
  ring

/--
**Hückel theory for the cycle `C₇`.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₇`
(equivalently, `α + μ·β` is a Hückel energy level of the corresponding annulene) if and
only if `μ = 2·cos(2πk/7)` for some `k ∈ {0, …, 6}`.
-/
