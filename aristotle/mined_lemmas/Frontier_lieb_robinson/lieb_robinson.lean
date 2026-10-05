import Mathlib
/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

section Basic

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The inner derivation (adjoint action) `ad H x = H * x - x * H`. -/

theorem lieb_robinson
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (loc : ℤ → ℤ → A → Prop)
    (loc_mono : ∀ {p q p' q' : ℤ} {x : A}, p' ≤ p → q ≤ q' → loc p q x → loc p' q' x)
    (loc_comm : ∀ {p q p' q' : ℤ} {x y : A}, q < p' → loc p q x → loc p' q' y → x * y = y * x)
    (loc_zero : ∀ p q : ℤ, loc p q 0)
    (loc_add : ∀ {p q : ℤ} {x y : A}, loc p q x → loc p q y → loc p q (x + y))
    (loc_neg : ∀ {p q : ℤ} {x : A}, loc p q x → loc p q (-x))
    (loc_mul : ∀ {p q : ℤ} {x y : A}, loc p q x → loc p q y → loc p q (x * y))
    (Λ : Finset ℤ) (hh : ℤ → A) (H : A) (hH : H = ∑ z ∈ Λ, hh z)
    (hhloc : ∀ z ∈ Λ, loc z (z + 1) (hh z))
    (a b : A) (pa qa pb qb : ℤ) (d : ℕ)
    (ha : loc pa qa a) (hb : loc pb qb b) (hd : qa + d ≤ pb) (t : ℝ) :
    ‖tau H t a * b - b * tau H t a‖
      ≤ 2 * ‖a‖ * ‖b‖ * ((2 * ‖H‖ * |t|) ^ d / (d ! : ℝ)) * Real.exp (2 * ‖H‖ * |t|) := by
  rw [tau_commutator_eq H t a b]
  set x : ℝ := 2 * ‖H‖ * |t| with hxdef
  set C : ℝ := 2 * ‖a‖ * ‖b‖ with hCdef
  have hx0 : (0:ℝ) ≤ x := by rw [hxdef]; positivity
  have hC0 : (0:ℝ) ≤ C := by rw [hCdef]; positivity
  set g : ℕ → A := fun n => (t ^ n / (n ! : ℝ)) • ((ad H)^[n] a * b - b * (ad H)^[n] a)
    with hgdef
  set M : ℕ → ℝ := fun n => if n < d then 0 else C * (x ^ n / (n ! : ℝ)) with hMdef
  have hgle : ∀ n : ℕ, ‖g n‖ ≤ C * (x ^ n / (n ! : ℝ)) := fun n => norm_term_le H t a b n
  have hgzero : ∀ n : ℕ, n < d → g n = 0 := by
    intro n hn
    have hloc := adPow_loc loc loc_mono loc_comm loc_zero loc_add loc_neg loc_mul Λ hh H hH
      hhloc ha n
    have hlt : qa + (n : ℤ) < pb := by
      have hnd : (n : ℤ) < (d : ℤ) := by exact_mod_cast hn
      omega
    have hcomm := loc_comm hlt hloc hb
    simp [hgdef, hcomm]
  have hMle : ∀ n : ℕ, ‖g n‖ ≤ M n := by
    intro n
    by_cases hn : n < d
    · simp [hMdef, hn, hgzero n hn]
    · simpa [hMdef, hn] using hgle n
  have hMsummable : Summable M := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      ((Real.summable_pow_div_factorial x).mul_left C)
    · by_cases hn : n < d
      · simp [hMdef, hn]
      · simp only [hMdef, hn, if_false]
        positivity
    · by_cases hn : n < d
      · simp only [hMdef, hn, if_true]
        positivity
      · simp [hMdef, hn]
  have hgsummable : Summable (fun n : ℕ => ‖g n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hMle hMsummable
  have hMsum : ∑' n : ℕ, M n ≤ C * ((x ^ d / (d ! : ℝ)) * Real.exp x) := by
    have hsplit := hMsummable.sum_add_tsum_nat_add d
    have hz : ∑ i ∈ Finset.range d, M i = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      simp [hMdef, Finset.mem_range.mp hi]
    have hshift : (fun k : ℕ => M (k + d)) = fun k : ℕ => C * (x ^ (k + d) / (((k + d)!) : ℝ)) := by
      funext k
      simp [hMdef]
    rw [← hsplit, hz, zero_add, hshift, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_exp_tail_le hx0 d) hC0
  calc ‖∑' n : ℕ, g n‖
      ≤ ∑' n : ℕ, ‖g n‖ := norm_tsum_le_tsum_norm hgsummable
    _ ≤ ∑' n : ℕ, M n := hgsummable.tsum_le_tsum hMle hMsummable
    _ ≤ C * ((x ^ d / (d ! : ℝ)) * Real.exp x) := hMsum
    _ = C * (x ^ d / (d ! : ℝ)) * Real.exp x := by ring

end Frontier

