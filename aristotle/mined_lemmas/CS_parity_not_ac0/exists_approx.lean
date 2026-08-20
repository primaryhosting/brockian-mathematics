import RequestProject.Basic

/-!
# Unbounded fan-in Boolean circuits, the class `AC⁰`, and `PARITY`

A `Circuit n` is a Boolean circuit on `n` inputs built from constants, input
variables, negations, and *unbounded fan-in* `AND`/`OR` gates.

* `Circuit.depth` counts the maximal number of `AND`/`OR` gates on a root-to-leaf
  path (negations are free, as is standard for `AC⁰`).
* `Circuit.size` counts the number of `AND`/`OR` gates.

`InAC0 f` says that the family `f` is computed by circuits of some fixed depth and
polynomial size.  Making negations free and not counting them in the size only
makes the class larger, hence the lower bound proved later stronger.
-/

namespace CS

/-- Boolean circuits with unbounded fan-in `AND`/`OR` gates. -/
inductive Circuit (n : ℕ) where
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | neg : Circuit n → Circuit n
  | or : (m : ℕ) → (Fin m → Circuit n) → Circuit n
  | and : (m : ℕ) → (Fin m → Circuit n) → Circuit n

namespace Circuit

/-- The Boolean function computed by a circuit. -/

theorem exists_approx {n : ℕ} (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (C : Circuit n) :
    ∃ f : Fn n, f ∈ Deg n ((2 * ℓ) ^ C.depth) ∧ (∀ x, f x = 0 ∨ f x = 1) ∧
      ((Finset.univ : Finset (Bits n)).filter (fun x => f x ≠ bit (C.eval x))).card * 3 ^ ℓ
        ≤ C.size * 2 ^ n := by
  classical
  induction C with
  | const b =>
      refine ⟨(bit b) • (1 : Fn n), Submodule.smul_mem _ _ one_mem_Deg, ?_, ?_⟩
      · intro x
        simpa using bit_eq_zero_or_one b
      · have : ((Finset.univ : Finset (Bits n)).filter
            (fun x => ((bit b) • (1 : Fn n)) x ≠ bit ((Circuit.const b).eval x))) = ∅ := by
          ext x; simp
        rw [this]
        simp
  | var i =>
      refine ⟨(2 : ZMod 3) • ((1 : Fn n) - mon ({i} : Finset (Fin n))), ?_, ?_, ?_⟩
      · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ one_mem_Deg (mon_mem_Deg (by simp)))
      · intro x
        cases hxi : x i
        · left; simp [Pi.smul_apply, Pi.sub_apply, mon, hxi, sgn]
        · right; simp [Pi.smul_apply, Pi.sub_apply, mon, hxi, sgn]; decide
      · have : ((Finset.univ : Finset (Bits n)).filter
            (fun x => ((2 : ZMod 3) • ((1 : Fn n) - mon ({i} : Finset (Fin n)))) x
              ≠ bit ((Circuit.var i).eval x))) = ∅ := by
          ext x
          cases hxi : x i
          · simp [Pi.smul_apply, Pi.sub_apply, mon, hxi, sgn, bit]
          · simp [Pi.smul_apply, Pi.sub_apply, mon, hxi, sgn, bit]; decide
        rw [this]
        simp
  | neg C ih =>
      obtain ⟨f, hf1, hf2, hf3⟩ := ih
      refine ⟨(1 : Fn n) - f, Submodule.sub_mem _ one_mem_Deg hf1, ?_, ?_⟩
      · intro x
        rcases hf2 x with h | h <;> simp [Pi.sub_apply, h]
      · have heq : ((Finset.univ : Finset (Bits n)).filter
            (fun x => ((1 : Fn n) - f) x ≠ bit ((Circuit.neg C).eval x)))
            = (Finset.univ : Finset (Bits n)).filter (fun x => f x ≠ bit (C.eval x)) := by
          have := filter_bad_neg f (fun x => C.eval x)
          simpa [Pi.sub_apply] using this
        rw [heq]
        simpa using hf3
  | or m g ih =>
      choose f hf1 hf2 hf3 using ih
      set Dm : ℕ := Finset.univ.sup (fun i => (g i).depth) with hDm
      have hfE : ∀ i, f i ∈ Deg n ((2 * ℓ) ^ Dm) := by
        intro i
        refine Deg_mono (Nat.pow_le_pow_right (by omega) ?_) (hf1 i)
        exact Finset.le_sup (f := fun i => (g i).depth) (Finset.mem_univ i)
      obtain ⟨F, hF1, hF2, hF3⟩ := exists_or_approx (ℓ := ℓ) f hfE hf2
      refine ⟨F, ?_, hF2, ?_⟩
      · have : 2 * ℓ * (2 * ℓ) ^ Dm = (2 * ℓ) ^ (Circuit.or m g).depth := by
          rw [Circuit.depth_or, ← hDm, add_comm 1 Dm, pow_succ]
          ring
        rwa [this] at hF1
      · have hcorr : ∀ x, (∀ i, f i x = bit ((g i).eval x)) →
            F x = bit (decide (∃ i, f i x = 1)) → F x = bit ((Circuit.or m g).eval x) := by
          intro x hall hFx
          rw [hFx, Circuit.eval_or]
          congr 1
          refine decide_eq_decide.2 ?_
          constructor
          · rintro ⟨i, hi⟩
            exact ⟨i, by rw [hall i] at hi; exact (bit_eq_one_iff _).1 hi⟩
          · rintro ⟨i, hi⟩
            exact ⟨i, by rw [hall i, hi]; rfl⟩
        have hbc := bad_card_le F (fun x => (Circuit.or m g).eval x) f
          (fun i x => (g i).eval x) hcorr
        calc ((Finset.univ : Finset (Bits n)).filter
              (fun x => F x ≠ bit ((Circuit.or m g).eval x))).card * 3 ^ ℓ
            ≤ (((Finset.univ : Finset (Bits n)).filter
                (fun x => F x ≠ bit (decide (∃ i, f i x = 1)))).card +
              ∑ i, ((Finset.univ : Finset (Bits n)).filter
                (fun x => f i x ≠ bit ((g i).eval x))).card) * 3 ^ ℓ :=
              Nat.mul_le_mul_right _ hbc
          _ = ((Finset.univ : Finset (Bits n)).filter
                (fun x => F x ≠ bit (decide (∃ i, f i x = 1)))).card * 3 ^ ℓ +
              ∑ i, ((Finset.univ : Finset (Bits n)).filter
                (fun x => f i x ≠ bit ((g i).eval x))).card * 3 ^ ℓ := by
              rw [add_mul, Finset.sum_mul]
          _ ≤ 2 ^ n + ∑ i, (g i).size * 2 ^ n :=
              Nat.add_le_add hF3 (Finset.sum_le_sum (fun i _ => hf3 i))
          _ = (1 + ∑ i, (g i).size) * 2 ^ n := by rw [add_mul, Finset.sum_mul]; ring
          _ = (Circuit.or m g).size * 2 ^ n := by rw [Circuit.size_or]
  | and m g ih =>
      choose f hf1 hf2 hf3 using ih
      set Dm : ℕ := Finset.univ.sup (fun i => (g i).depth) with hDm
      have hfE : ∀ i, ((1 : Fn n) - f i) ∈ Deg n ((2 * ℓ) ^ Dm) := by
        intro i
        refine Submodule.sub_mem _ one_mem_Deg (Deg_mono (Nat.pow_le_pow_right (by omega) ?_)
          (hf1 i))
        exact Finset.le_sup (f := fun i => (g i).depth) (Finset.mem_univ i)
      have hq01 : ∀ i x, ((1 : Fn n) - f i) x = 0 ∨ ((1 : Fn n) - f i) x = 1 := by
        intro i x
        rcases hf2 i x with h | h <;> simp [Pi.sub_apply, h]
      obtain ⟨F, hF1, hF2, hF3⟩ := exists_or_approx (ℓ := ℓ) (fun i => (1 : Fn n) - f i) hfE hq01
      refine ⟨(1 : Fn n) - F, ?_, ?_, ?_⟩
      · have hpow : 2 * ℓ * (2 * ℓ) ^ Dm = (2 * ℓ) ^ (Circuit.and m g).depth := by
          rw [Circuit.depth_and, ← hDm, add_comm 1 Dm, pow_succ]
          ring
        rw [hpow] at hF1
        exact Submodule.sub_mem _ one_mem_Deg hF1
      · intro x
        rcases hF2 x with h | h <;> simp [Pi.sub_apply, h]
      · have hcorr : ∀ x, (∀ i, ((1 : Fn n) - f i) x = bit (!((g i).eval x))) →
            F x = bit (decide (∃ i, ((1 : Fn n) - f i) x = 1)) →
            F x = bit (!((Circuit.and m g).eval x)) := by
          intro x hall hFx
          rw [hFx, Circuit.eval_and]
          congr 1
          rw [← decide_not]
          refine decide_eq_decide.2 ?_
          constructor
          · rintro ⟨i, hi⟩ hcon
            rw [hall i] at hi
            have h1 : (!((g i).eval x)) = true := (bit_eq_one_iff _).1 hi
            rw [hcon i] at h1
            exact Bool.noConfusion h1
          · intro hcon
            simp only [not_forall] at hcon
            obtain ⟨i, hi⟩ := hcon
            refine ⟨i, ?_⟩
            rw [hall i]
            have hgi : (g i).eval x = false := by
              cases h : (g i).eval x
              · rfl
              · exact absurd h hi
            rw [hgi]
            rfl
        have hbc := bad_card_le F (fun x => !((Circuit.and m g).eval x))
          (fun i => (1 : Fn n) - f i) (fun i x => !((g i).eval x)) hcorr
        have hbadneg : ((Finset.univ : Finset (Bits n)).filter
            (fun x => ((1 : Fn n) - F) x ≠ bit ((Circuit.and m g).eval x)))
            = (Finset.univ : Finset (Bits n)).filter
              (fun x => F x ≠ bit (!((Circuit.and m g).eval x))) := by
          apply Finset.filter_congr
          intro x _
          rw [Pi.sub_apply, Pi.one_apply, bit_not]
          constructor
          · intro h hc
            exact h (by rw [hc]; ring)
          · intro h hc
            exact h (by rw [← hc]; ring)
        have hchild : ∀ i, ((Finset.univ : Finset (Bits n)).filter
            (fun x => ((1 : Fn n) - f i) x ≠ bit (!((g i).eval x))))
            = (Finset.univ : Finset (Bits n)).filter (fun x => f i x ≠ bit ((g i).eval x)) := by
          intro i
          have := filter_bad_neg (f i) (fun x => (g i).eval x)
          simpa [Pi.sub_apply] using this
        rw [hbadneg]
        calc ((Finset.univ : Finset (Bits n)).filter
              (fun x => F x ≠ bit (!((Circuit.and m g).eval x)))).card * 3 ^ ℓ
            ≤ (((Finset.univ : Finset (Bits n)).filter
                (fun x => F x ≠ bit (decide (∃ i, ((1 : Fn n) - f i) x = 1)))).card +
              ∑ i, ((Finset.univ : Finset (Bits n)).filter
                (fun x => ((1 : Fn n) - f i) x ≠ bit (!((g i).eval x)))).card) * 3 ^ ℓ :=
              Nat.mul_le_mul_right _ hbc
          _ = ((Finset.univ : Finset (Bits n)).filter
                (fun x => F x ≠ bit (decide (∃ i, ((1 : Fn n) - f i) x = 1)))).card * 3 ^ ℓ +
              ∑ i, ((Finset.univ : Finset (Bits n)).filter
                (fun x => f i x ≠ bit ((g i).eval x))).card * 3 ^ ℓ := by
              rw [add_mul, Finset.sum_mul]
              congr 1
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [hchild i]
          _ ≤ 2 ^ n + ∑ i, (g i).size * 2 ^ n :=
              Nat.add_le_add hF3 (Finset.sum_le_sum (fun i _ => hf3 i))
          _ = (1 + ∑ i, (g i).size) * 2 ^ n := by rw [add_mul, Finset.sum_mul]; ring
          _ = (Circuit.and m g).size * 2 ^ n := by rw [Circuit.size_and]

end CS

import Mathlib

/-!
# Basic setup: the space of `ZMod 3`-valued functions on the Boolean cube

We encode a Boolean value `b` by the sign `sgn b = (-1)^b ∈ ZMod 3`, so that the
Boolean cube becomes `{1, -1}^n ⊆ (ZMod 3)^n`.  For `T ⊆ Fin n` the monomial
function `mon T` is `x ↦ ∏_{i ∈ T} sgn (x i)`, and `Deg n k` is the `ZMod 3`-span
of the monomials of degree at most `k`.  This is the ambient algebra used for the
Razborov–Smolensky approximation method.
-/

namespace CS

open Finset

/-- Boolean inputs. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- `ZMod 3`-valued functions on the Boolean cube. -/
abbrev Fn (n : ℕ) := Bits n → ZMod 3

/-- The `±1` encoding of a Boolean value inside `ZMod 3`. -/
