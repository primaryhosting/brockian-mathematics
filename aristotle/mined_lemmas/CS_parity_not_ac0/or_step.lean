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
import RequestProject.PolySpace

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Unbounded fan-in Boolean circuits and their low-degree approximation

We define constant-depth, unbounded fan-in Boolean circuits over the basis
`{¬, ∨, ∧}` and prove Razborov's approximation lemma: a circuit of size `s`
and depth `d` is computed by a function of `F₃`-degree at most `(2ℓ)^d`
on all but a `s·2^{-ℓ}` fraction of the inputs.
-/

namespace CS

open Finset

/-- Unbounded fan-in Boolean circuits on `n` inputs. -/
inductive Circ (n : ℕ) where
  | var : Fin n → Circ n
  | cst : Bool → Circ n
  | neg : Circ n → Circ n
  | orG : (k : ℕ) → (Fin k → Circ n) → Circ n
  | andG : (k : ℕ) → (Fin k → Circ n) → Circ n

/-- The Boolean function computed by a circuit. -/

lemma or_step {n : ℕ} (k ℓ D : ℕ) (g : Fin k → Fn n) (hg : ∀ i, g i ∈ V n D)
    (b : Fin k → Inp n → Bool) (U : Finset (Inp n))
    (hU : ∀ x ∈ U, ∀ i, g i x = bf (b i x)) :
    ∃ G ∈ V n (2 * ℓ * D),
      (U.filter (fun x => G x ≠ bf (decide (∃ i, b i x = true)))).card * 2 ^ ℓ ≤ U.card := by
  classical
  -- the set of choices
  set R : Finset (Fin ℓ → Fin k → Bool) := Finset.univ with hR
  have hRcard : R.card = (2 ^ k) ^ ℓ := by
    rw [hR, Finset.card_univ, Fintype.card_fun, Fintype.card_fun]
    simp
  -- for each fixed input, few choices are bad
  have key : ∀ x ∈ U, ((R.filter
      (fun r => orApprox g r x ≠ bf (decide (∃ i, b i x = true)))).card) * 2 ^ ℓ ≤ R.card := by
    intro x hx
    by_cases hex : ∃ i, b i x = true
    · obtain ⟨i₀, hi₀⟩ := hex
      set v : Fin k → F3 := fun i => g i x with hv
      have hv₀ : v i₀ = 1 := by rw [hv]; simp [hU x hx i₀, hi₀]
      set Z := (Finset.univ.filter
          (fun a : Fin k → Bool => ∑ i, (if a i then v i else 0) = 0)) with hZ
      have hZhalf : 2 * Z.card ≤ 2 ^ k := card_zero_subset_sums v i₀ hv₀
      -- bad choices all lie in the product set `Z^ℓ`
      have hsub : (R.filter (fun r => orApprox g r x ≠ bf (decide (∃ i, b i x = true))))
          ⊆ Fintype.piFinset (fun _ : Fin ℓ => Z) := by
        intro r hr
        simp only [Finset.mem_filter] at hr
        refine Fintype.mem_piFinset.2 (fun j => ?_)
        by_contra hj
        have hjne : (∑ i, (if r j i then v i else 0)) ≠ 0 := by
          simpa [hZ] using hj
        have : orApprox g r x = 1 := by
          rw [orApprox_apply]
          have : (∏ j : Fin ℓ, (1 - (∑ i : Fin k, (if r j i then g i x else 0)) ^ 2)) = 0 := by
            refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
            have hsq : (∑ i : Fin k, (if r j i then v i else 0)) ^ 2 = 1 := by
              revert hjne
              generalize (∑ i : Fin k, (if r j i then v i else 0)) = c
              decide +revert
            rw [show (∑ i : Fin k, (if r j i then g i x else 0))
                = (∑ i : Fin k, (if r j i then v i else 0)) from rfl, hsq]
            ring
          rw [this]; ring
        rw [this] at hr
        have : bf (decide (∃ i, b i x = true)) = 1 := by
          simp only [bf, decide_eq_true_eq, if_pos (⟨i₀, hi₀⟩ : ∃ i, b i x = true)]
        exact hr.2 (by rw [this])
      have hcard := Finset.card_le_card hsub
      rw [Fintype.card_piFinset] at hcard
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcard
      calc (R.filter (fun r => orApprox g r x ≠ bf (decide (∃ i, b i x = true)))).card * 2 ^ ℓ
          ≤ Z.card ^ ℓ * 2 ^ ℓ := Nat.mul_le_mul_right _ hcard
        _ = (Z.card * 2) ^ ℓ := by rw [mul_pow]
        _ ≤ (2 ^ k) ^ ℓ := Nat.pow_le_pow_left (by omega) ℓ
        _ = R.card := hRcard.symm
    · -- the OR is false: the approximator is exactly correct
      have hall : ∀ i, b i x = false := by
        intro i; cases h : b i x
        · rfl
        · exact absurd ⟨i, h⟩ hex
      have hzero : ∀ r : Fin ℓ → Fin k → Bool, orApprox g r x = 0 := by
        intro r
        rw [orApprox_apply]
        have : ∀ j : Fin ℓ, (1 - (∑ i : Fin k, (if r j i then g i x else 0)) ^ 2) = 1 := by
          intro j
          have : (∑ i : Fin k, (if r j i then g i x else 0)) = 0 := by
            refine Finset.sum_eq_zero (fun i _ => ?_)
            by_cases h : r j i
            · simp [h, hU x hx i, hall i]
            · simp [h]
          rw [this]; ring
        rw [Finset.prod_congr rfl (fun j _ => this j)]
        simp
      have : (R.filter (fun r => orApprox g r x ≠ bf (decide (∃ i, b i x = true)))) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 (fun r _ => ?_)
        rw [hzero r]
        simp [bf, hex]
      rw [this]
      simp
  -- double counting
  have hdc : ∑ r ∈ R, ((U.filter (fun x => orApprox g r x ≠ bf (decide (∃ i, b i x = true)))).card
        * 2 ^ ℓ) ≤ ∑ _r ∈ R, U.card := by
    have hswap : ∑ r ∈ R, (U.filter (fun x => orApprox g r x
          ≠ bf (decide (∃ i, b i x = true)))).card
        = ∑ x ∈ U, (R.filter (fun r => orApprox g r x
          ≠ bf (decide (∃ i, b i x = true)))).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    calc ∑ r ∈ R, ((U.filter (fun x => orApprox g r x
              ≠ bf (decide (∃ i, b i x = true)))).card * 2 ^ ℓ)
        = (∑ r ∈ R, (U.filter (fun x => orApprox g r x
              ≠ bf (decide (∃ i, b i x = true)))).card) * 2 ^ ℓ := by
          rw [Finset.sum_mul]
      _ = (∑ x ∈ U, (R.filter (fun r => orApprox g r x
              ≠ bf (decide (∃ i, b i x = true)))).card) * 2 ^ ℓ := by rw [hswap]
      _ = ∑ x ∈ U, ((R.filter (fun r => orApprox g r x
              ≠ bf (decide (∃ i, b i x = true)))).card * 2 ^ ℓ) := by rw [Finset.sum_mul]
      _ ≤ ∑ _x ∈ U, R.card := Finset.sum_le_sum key
      _ = U.card * R.card := by rw [Finset.sum_const, smul_eq_mul]
      _ = ∑ _r ∈ R, U.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  obtain ⟨r, _, hr⟩ := Finset.exists_le_of_sum_le ⟨(fun _ _ => false), Finset.mem_univ _⟩ hdc
  exact ⟨orApprox g r, orApprox_mem g hg r, hr⟩

end CS

import Mathlib

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The space of `F₃`-valued functions on the Boolean cube

We set up the "low degree" filtration of the space of functions
`(Fin n → Bool) → ZMod 3`, both in the `x`-coordinates (`x i ∈ {0,1}`)
and in the `y`-coordinates (`y i = 1 + x i ∈ {1,-1}`), and show that the two
filtrations coincide.
-/

namespace CS

open Finset

/-- The field with three elements. -/
abbrev F3 := ZMod 3

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Booleans as elements of `F₃`. -/
