/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized here

Belyi's theorem is formalized in its genus-zero (polynomial) form, which is the arithmetic heart
of the theorem: the "curve" is the projective line together with a finite set `S` of marked
complex points, and a Belyi map is given by a polynomial `f ∈ ℚ[X]` — viewed as a map
`ℙ¹ → ℙ¹` defined over `ℚ` for which `∞` is totally ramified over `∞`.

`Math2.belyi_theorem` states that the marked points are defined over `ℚ̄` (i.e. all elements of
`S` are algebraic over `ℚ`) if and only if there is a nonconstant such `f` which maps `S` into
`{0, 1}` and all of whose critical values lie in `{0, 1}`, i.e. which is unramified outside
`{0, 1, ∞}`.

The easy direction is elementary. The hard direction is Belyi's algorithm, carried out here in
two stages:

* `Math2.stageA`: composing with minimal polynomials, one finds a nonconstant `f ∈ ℚ[X]` for
  which the images of the marked points and all critical values are rational. Termination is
  measured by `Math2.muA`, a sum of factorials of the degrees of the algebraic numbers involved.
* `Math2.stageB`: a finite set of rationals is collapsed into `{0, 1}` by repeatedly composing
  with the polynomials `c · x^m (1-x)^n` (after an affine change of coordinates), each step
  strictly decreasing the number of relevant rational values.
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

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Critical points and critical values -/

/-- The critical points in `ℂ` of a polynomial with rational coefficients. -/

lemma muA_step {s0 : ℂ} {S : Finset ℂ} (hS : ∀ z ∈ S, IsAlgebraic ℚ z) (hs0S : s0 ∈ S)
    (hd : 2 ≤ degQ s0) :
    muA (S.image (fun z => aeval z (minpoly ℚ s0)) ∪ critVals (minpoly ℚ s0)) < muA S := by
  set mp : ℚ[X] := minpoly ℚ s0 with hmp
  set d : ℕ := mp.natDegree with hdd
  have hdegs0 : degQ s0 = d := rfl
  have hd2 : 2 ≤ d := by rw [← hdegs0]; exact hd
  have hmp1 : 1 ≤ mp.natDegree := by omega
  have h1 : muA (S.image (fun z => aeval z mp) ∪ critVals mp)
      ≤ muA (S.image (fun z => aeval z mp)) + muA (critVals mp) := by
    simp only [muA]
    have h := Finset.sum_union_inter (s₁ := S.image (fun z => aeval z mp)) (s₂ := critVals mp)
      (f := fun z => (degQ z + 1)!)
    omega
  have h2 : muA (S.image (fun z => aeval z mp)) ≤ ∑ z ∈ S, (degQ (aeval z mp) + 1)! :=
    Finset.sum_image_le_of_nonneg (fun u _ => Nat.zero_le _)
  have h3 : ∑ z ∈ S, (degQ (aeval z mp) + 1)!
      = (degQ (aeval s0 mp) + 1)! + ∑ z ∈ S.erase s0, (degQ (aeval z mp) + 1)! :=
    (Finset.add_sum_erase S _ hs0S).symm
  have h4 : (degQ (aeval s0 mp) + 1)! = 2 := by
    rw [show aeval s0 mp = 0 from minpoly.aeval ℚ s0, degQ_zero]
    rfl
  have h5 : ∑ z ∈ S.erase s0, (degQ (aeval z mp) + 1)! ≤ ∑ z ∈ S.erase s0, (degQ z + 1)! :=
    Finset.sum_le_sum (fun z hz => Nat.factorial_le (by
      have := degQ_aeval_le (hS z (Finset.mem_of_mem_erase hz)) mp; omega))
  have hcritbd : ∀ y ∈ critVals mp, (degQ y + 1)! ≤ d ! := by
    intro y hy
    simp only [critVals, Finset.mem_image] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hwalg : IsAlgebraic ℚ w := isAlgebraic_of_mem_critPts hmp1 hw
    have hwd : degQ w ≤ d - 1 := by
      have hle := degQ_le_of_aeval_eq_zero (derivative_ne_zero_of_one_le_natDegree hmp1)
        (aeval_eq_zero_of_mem_critPts hw)
      have := Polynomial.natDegree_derivative_le mp
      omega
    have hle2 := degQ_aeval_le hwalg mp
    exact Nat.factorial_le (by omega)
  have h6 : muA (critVals mp) ≤ (critVals mp).card * d ! := by
    simpa [muA, smul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hcritbd
  have h7 : (critVals mp).card ≤ d - 1 :=
    le_trans Finset.card_image_le (card_critPts_le mp)
  have h8 : muA S = (d + 1)! + ∑ z ∈ S.erase s0, (degQ z + 1)! := by
    simp only [muA]
    rw [← Finset.add_sum_erase S _ hs0S, hdegs0]
  have h9 : (critVals mp).card * d ! ≤ (d - 1) * d ! := Nat.mul_le_mul_right _ h7
  have key := factorial_ineq hd2
  omega

