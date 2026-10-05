/-
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

/-! ## A ℚ-linear functional that is positive on a finite family of positive reals -/

/-- Given finitely many *positive* real numbers `x s`, there is a `ℚ`-linear functional
`f : ℝ →ₗ[ℚ] ℚ` which is positive on all of them.  (Such an `f` is a rational
"approximation of the identity" on the `ℚ`-span of the `x s`.) -/

theorem exists_pos_int_null {E S : Type*} [Fintype S] (A : Matrix E S ℤ) (y : S → ℚ)
    (hy : ∀ s, 0 < y s) (h : ∀ e, ∑ s, (A e s : ℚ) * y s = 0) :
    ∃ n : S → ℤ, (∀ s, 0 < n s) ∧ ∀ e, ∑ s, A e s * n s = 0 := by
  classical
  set d : ℕ := ∏ s, (y s).den with hd
  have hdpos : 0 < d := Finset.prod_pos fun s _ => (y s).pos
  have key : ∀ s, ((d : ℚ)) * y s = ((((d : ℚ)) * y s).num : ℚ) := by
    intro s
    obtain ⟨k, hk⟩ : (y s).den ∣ d :=
      Finset.dvd_prod_of_mem (fun t => (y t).den) (Finset.mem_univ s)
    have hz : ∃ z : ℤ, ((d : ℚ)) * y s = (z : ℚ) := by
      refine ⟨k * (y s).num, ?_⟩
      have hstep : ((d : ℚ)) * y s = (k : ℚ) * (((y s).den : ℚ) * y s) := by
        rw [hk]; push_cast; ring
      rw [hstep, Rat.den_mul_eq_num]
      push_cast; ring
    obtain ⟨z, hzz⟩ := hz
    rw [hzz, Rat.num_intCast]
  refine ⟨fun s => (((d : ℚ)) * y s).num, fun s => ?_, fun e => ?_⟩
  · have hpos : (0:ℚ) < ((((d : ℚ)) * y s).num : ℚ) := by
      rw [← key s]
      exact mul_pos (by exact_mod_cast hdpos) (hy s)
    exact_mod_cast hpos
  · have hcast : ((∑ s, A e s * (((d : ℚ)) * y s).num : ℤ) : ℚ) = 0 := by
      push_cast
      have hstep : ∑ s, (A e s : ℚ) * ((((d : ℚ)) * y s).num : ℚ)
          = (d : ℚ) * ∑ s, (A e s : ℚ) * y s := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← key s]; ring
      rw [hstep, h e, mul_zero]
    exact_mod_cast hcast

/-! ## The linear-algebra core -/

/-- For an integer matrix `A`, having a coordinatewise positive *real* null vector is
equivalent to having a coordinatewise positive *integer* null vector. -/
