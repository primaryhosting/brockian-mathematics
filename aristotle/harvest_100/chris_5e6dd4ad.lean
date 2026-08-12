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

namespace QC

/-- Bitstrings of length 5, indexing the computational basis of a 5-qubit register. -/
abbrev Bits5 := Fin 5 → Fin 2

/-- The predicate picking out the two basis states `|00000⟩` and `|11111⟩`. -/
def AllEqual (b : Bits5) : Prop := (∀ i, b i = 0) ∨ (∀ i, b i = 1)

instance (b : Bits5) : Decidable (AllEqual b) := by
  unfold AllEqual; infer_instance

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector in the
Hilbert space `EuclideanSpace ℂ Bits5` of dimension `2 ^ 5 = 32`. -/
noncomputable def ghz5 : EuclideanSpace ℂ Bits5 :=
  WithLp.toLp 2 (fun b => if AllEqual b then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- `AllEqual` holds exactly for the two constant bitstrings. -/
theorem allEqual_iff (b : Bits5) :
    AllEqual b ↔ (b = fun _ => (0 : Fin 2)) ∨ (b = fun _ => (1 : Fin 2)) := by
  simp [AllEqual, funext_iff]

/-- `ghz5` really is `(|00000⟩ + |11111⟩)/√2`: it is the normalizing scalar `1/√2`
times the sum of the two computational basis vectors `|00000⟩` and `|11111⟩`. -/
theorem ghz5_eq :
    ghz5 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single (fun _ => (0 : Fin 2)) (1 : ℂ)
        + EuclideanSpace.single (fun _ => (1 : Fin 2)) (1 : ℂ)) := by
  have hzo : ((fun _ => (0 : Fin 2)) : Bits5) ≠ (fun _ => (1 : Fin 2)) := by decide
  ext b
  simp only [ghz5, WithLp.ofLp_toLp, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
    EuclideanSpace.single_apply]
  rcases eq_or_ne b (fun _ => (0 : Fin 2)) with h | h0
  · subst h
    rw [if_pos ((allEqual_iff _).2 (Or.inl rfl)), if_pos rfl, if_neg hzo]
    ring
  · rcases eq_or_ne b (fun _ => (1 : Fin 2)) with h | h1
    · subst h
      rw [if_pos ((allEqual_iff _).2 (Or.inr rfl)), if_neg (Ne.symm hzo), if_pos rfl]
      ring
    · rw [if_neg (fun h => ((allEqual_iff b).1 h).elim h0 h1), if_neg h0, if_neg h1]
      ring

theorem card_allEqual : (Finset.univ.filter AllEqual).card = 2 := by
  decide

theorem sq_norm_ghz5 (b : Bits5) :
    ‖(WithLp.ofLp ghz5) b‖ ^ 2 = if AllEqual b then (1 / 2 : ℝ) else 0 := by
  unfold ghz5
  rw [WithLp.ofLp_toLp]
  split
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow,
      Real.sq_sqrt (by norm_num)]
    norm_num
  · simp

/-- The 5-qubit GHZ state is a unit vector. -/
theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp_rw [sq_norm_ghz5]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, card_allEqual]
  norm_num

end QC

