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

/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module doc-comment, so the header
-- above is repeated as the module documentation just after the import.)
import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Shannon entropy of a finite distribution (in nats) -/

/-- Shannon entropy (in nats) of a distribution `p` on a finite type,
using the standard convention `0 * log 0 = 0`. -/

theorem landauer_erasure_example :
    ∃ (E : Fin 4 → ℝ) (pS : Bool → ℝ) (q : Bool × Fin 4 → ℝ) (qS : Bool → ℝ) (Q : ℝ),
      (∀ s, pS s = if s = false ∨ s = true then 1 / 2 else 0) ∧
      (∀ x, 0 ≤ q x) ∧
      (∑ x, q x = 1) ∧
      entropy (fun y : Bool × Fin 4 => pS y.1 * gibbs (1 / ((1 : ℝ) * 1)) E y.2) ≤ entropy q ∧
      (∀ s, qS s = ∑ r, q (s, r)) ∧
      qS true = 1 ∧
      Q = (∑ x, q x * E x.2) - ∑ r, gibbs (1 / ((1 : ℝ) * 1)) E r * E r ∧
      (1 : ℝ) * 1 * Real.log 2 ≤ Q := by
  have hbeta : (1 : ℝ) / ((1 : ℝ) * 1) = 1 := by norm_num
  set pS : Bool → ℝ := fun _ => 1 / 2 with hpSdef
  set q : Bool × Fin 4 → ℝ := fun x => if x.1 = true then 1 / 4 else 0 with hqdef
  set qS : Bool → ℝ := fun s => if s = true then 1 else 0 with hqSdef
  have hpS : ∀ s : Bool, pS s = if s = false ∨ s = true then (1 : ℝ) / 2 else 0 := by
    intro s; cases s <;> simp [hpSdef]
  have hq0 : ∀ x : Bool × Fin 4, 0 ≤ q x := by intro x; simp only [hqdef]; positivity
  have hq1 : ∑ x : Bool × Fin 4, q x = 1 := by
    simp only [hqdef]; rw [Fintype.sum_prod_type]; simp
  have hqS : ∀ s : Bool, qS s = ∑ r : Fin 4, q (s, r) := by
    intro s; simp only [hqdef, hqSdef]; cases s <;> simp
  have herase : qS true = 1 := by simp [hqSdef]
  have hentq : entropy q = Real.log 4 := by
    simp only [hqdef, entropy]
    rw [Fintype.sum_prod_type]
    simp [Real.negMulLog]
  have hentp : entropy (fun y : Bool × Fin 4 => pS y.1 * gibbs 1 exampleEnergy y.2)
      = 2 * Real.negMulLog (9 / 20) + 6 * Real.negMulLog (1 / 60) := by
    simp only [hpSdef, entropy]
    rw [Fintype.sum_prod_type]
    simp [example_gibbs, Fin.sum_univ_four]
    ring_nf
  have hnum : 2 * Real.negMulLog (9 / 20) + 6 * Real.negMulLog (1 / 60) ≤ Real.log 4 := by
    have h1 : Real.log (9 / 20 : ℝ) = -Real.log (20 / 9) := by
      rw [show (9 / 20 : ℝ) = ((20 / 9 : ℝ))⁻¹ by norm_num, Real.log_inv]
    have h2 : Real.log (1 / 60 : ℝ) = -Real.log 60 := by
      rw [show (1 / 60 : ℝ) = ((60 : ℝ))⁻¹ by norm_num, Real.log_inv]
    have key : 9 * Real.log (20 / 9) + Real.log 60 ≤ 10 * Real.log 4 := by
      have hle : Real.log (((20 : ℝ) / 9) ^ 9 * 60) ≤ Real.log ((4 : ℝ) ^ 10) :=
        Real.log_le_log (by positivity) (by norm_num)
      rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow] at hle
      push_cast at hle
      linarith
    simp only [Real.negMulLog, h1, h2]
    linarith
  have hent : entropy (fun y : Bool × Fin 4 => pS y.1 * gibbs (1 / ((1 : ℝ) * 1)) exampleEnergy y.2)
      ≤ entropy q := by
    rw [hbeta, hentp, hentq]; exact hnum
  have hQ : (13 / 20) * Real.log 27
      = (∑ x : Bool × Fin 4, q x * exampleEnergy x.2)
        - ∑ r, gibbs (1 / ((1 : ℝ) * 1)) exampleEnergy r * exampleEnergy r := by
    rw [hbeta]
    simp only [hqdef]
    rw [Fintype.sum_prod_type]
    simp only [example_gibbs]
    simp [Fin.sum_univ_four, exampleEnergy]
    ring
  exact ⟨exampleEnergy, pS, q, qS, 13 / 20 * Real.log 27, hpS, hq0, hq1, hent, hqS, herase, hQ,
    landauer_principle 1 1 one_pos one_pos exampleEnergy false true (by simp) pS hpS q hq0 hq1
      hent qS hqS true herase _ hQ⟩

end Phys

