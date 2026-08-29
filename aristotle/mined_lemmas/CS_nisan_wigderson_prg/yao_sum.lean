import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace CS

open Finset

/-- Real-valued indicator of a boolean: `1` for `true`, `0` for `false`. -/

lemma yao_sum {n l m : ℕ} (S : Fin m → Fin l → Fin n) (f : (Fin l → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) (k : ℕ) (i : Fin m) (hi : (i : ℕ) = k) :
    ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, succTerm S f D k i x r
      = (2 : ℝ) ^ n * 2 ^ m / 2
        + (∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f (k + 1) x r)))
        - ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f k x r)) := by
  classical
  simp only [succTerm]
  set su : (Fin n → Bool) → (Fin m → Bool) → ℝ := fun x r =>
    (if xor (D (hyb S f k x r)) (!(r i)) = f (fun t => x (S i t)) then (1 : ℝ) else 0) with hsu
  set L : ℝ := ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, su x r with hL
  set A : ℝ := ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f (k + 1) x r)) with hA
  set B : ℝ := ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f k x r)) with hB
  have key : ∀ (x : Fin n → Bool) (r : Fin m → Bool),
      su x r + su x (Function.update r i (!(r i)))
        = 2 * bv (D (hyb S f (k + 1) x r)) - bv (D (hyb S f k x r))
          - bv (D (hyb S f k x (Function.update r i (!(r i))))) + 1 := by
    intro x r
    have hT : hyb S f (k + 1) x r i = f (fun t => x (S i t)) := hyb_apply_self S f k i hi x r
    have e1 : hyb S f k x r = Function.update (hyb S f (k + 1) x r) i (r i) :=
      hyb_eq_update S f k i hi x r
    have e2 : hyb S f k x (Function.update r i (!(r i)))
        = Function.update (hyb S f (k + 1) x r) i (!(r i)) := by
      rw [hyb_eq_update S f k i hi x (Function.update r i (!(r i))),
        hyb_succ_flip S f k i hi x r, Function.update_self]
    have e3 : Function.update (hyb S f (k + 1) x r) i (f (fun t => x (S i t)))
        = hyb S f (k + 1) x r := by
      rw [← hT, Function.update_eq_self]
    have hp := yao_pointwise D (hyb S f (k + 1) x r) i (f (fun t => x (S i t))) (r i)
    rw [e3] at hp
    simp only [hsu]
    rw [e1, e2, Function.update_self]
    exact hp
  have hflip1 : ∀ x : Fin n → Bool,
      ∑ r : Fin m → Bool, su x (Function.update r i (!(r i))) = ∑ r : Fin m → Bool, su x r :=
    fun x => sum_flip i (fun r => su x r)
  have hflip2 : ∀ x : Fin n → Bool,
      ∑ r : Fin m → Bool, bv (D (hyb S f k x (Function.update r i (!(r i)))))
        = ∑ r : Fin m → Bool, bv (D (hyb S f k x r)) :=
    fun x => sum_flip i (fun r => bv (D (hyb S f k x r)))
  have step1 : ∑ x : Fin n → Bool, ∑ r : Fin m → Bool,
      (su x r + su x (Function.update r i (!(r i))))
      = ∑ x : Fin n → Bool, ∑ r : Fin m → Bool,
        (2 * bv (D (hyb S f (k + 1) x r)) - bv (D (hyb S f k x r))
          - bv (D (hyb S f k x (Function.update r i (!(r i))))) + 1) :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun r _ => key x r
  have step2 : ∑ x : Fin n → Bool, ∑ r : Fin m → Bool,
      (su x r + su x (Function.update r i (!(r i)))) = 2 * L := by
    rw [hL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_add_distrib, hflip1 x, two_mul]
  have step3 : ∑ x : Fin n → Bool, ∑ r : Fin m → Bool,
      (2 * bv (D (hyb S f (k + 1) x r)) - bv (D (hyb S f k x r))
        - bv (D (hyb S f k x (Function.update r i (!(r i))))) + 1)
      = 2 * A - 2 * B + 2 ^ n * 2 ^ m := by
    have : ∀ x : Fin n → Bool, ∑ r : Fin m → Bool,
        (2 * bv (D (hyb S f (k + 1) x r)) - bv (D (hyb S f k x r))
          - bv (D (hyb S f k x (Function.update r i (!(r i))))) + 1)
        = 2 * (∑ r : Fin m → Bool, bv (D (hyb S f (k + 1) x r)))
          - 2 * (∑ r : Fin m → Bool, bv (D (hyb S f k x r))) + 2 ^ m := by
      intro x
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        hflip2 x, ← Finset.mul_sum]
      simp [two_mul]
      ring
    rw [Finset.sum_congr rfl fun x _ => this x]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hA, hB]
    simp [Finset.sum_const]
  rw [step2] at step1
  rw [step3] at step1
  linarith

/-- **Nisan–Wigderson reconstruction.**  If a distinguisher `D` tells the output of the
Nisan–Wigderson generator built from `f` and a combinatorial design `S` apart from uniform
with advantage more than `ε`, then `f` is computed on more than a `1/2 + ε/m` fraction of
its inputs by `D` composed with `α`-juntas (up to a fixed output flip `c`).  Here the design
condition is that any two distinct index sets `S i`, `S j` overlap in at most `α` positions. -/
