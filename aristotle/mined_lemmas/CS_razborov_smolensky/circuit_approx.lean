import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem circuit_approx {n : ℕ} (β : ℕ → Bool) (t : ℕ) (ht : 1 ≤ t) (C : Circuit) :
    ∃ P ∈ Deg F n ((t * (q - 1)) ^ C.depth),
      2 ^ t * #(errSet P (fun x => C.eval q (ext β x))) ≤ C.size * 2 ^ n := by
  classical
  have hq2 : 2 ≤ q := hq.out.two_le
  have hbase : 1 ≤ t * (q - 1) := by
    have := Nat.mul_le_mul ht (show 1 ≤ q - 1 by omega)
    simpa using this
  induction C using Circuit.induction with
  | hvar i =>
      simp only [Circuit.depth_var, pow_zero]
      by_cases h : i < n
      · refine ⟨fun x => bitv F (x ⟨i, h⟩), bit_var_mem_Deg _, ?_⟩
        have he : errSet (fun x : Cube n => bitv F (x ⟨i, h⟩))
            (fun x => (Circuit.var i).eval q (ext β x)) = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun x _ => ?_
          simp [ext, h]
        rw [errSet] at he ⊢
        rw [he]
        simp
      · refine ⟨fun _ => bitv F (β i), const_mem_Deg _, ?_⟩
        have he : errSet (fun _ : Cube n => bitv F (β i))
            (fun x => (Circuit.var i).eval q (ext β x)) = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun x _ => ?_
          simp [ext, h]
        rw [errSet] at he ⊢
        rw [he]
        simp
  | hconst b =>
      simp only [Circuit.depth_const, pow_zero]
      refine ⟨fun _ => bitv F b, const_mem_Deg _, ?_⟩
      have he : errSet (fun _ : Cube n => bitv F b)
          (fun x => (Circuit.const b).eval q (ext β x)) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun x _ => ?_
        simp
      rw [errSet] at he ⊢
      rw [he]
      simp
  | hnot c ihc =>
      obtain ⟨P, hP, hPe⟩ := ihc
      refine ⟨1 - P, ?_, ?_⟩
      · rw [Circuit.depth_cnot]
        exact Submodule.sub_mem _ one_mem_Deg hP
      · have hfun : (fun x : Cube n => (Circuit.cnot c).eval q (ext β x))
            = fun x => !(c.eval q (ext β x)) := by funext x; simp
        rw [hfun, errSet_one_sub]
        exact le_trans hPe (Nat.mul_le_mul_right _ (by simp))
  | hor cs ih =>
      obtain ⟨g, B, hgdeg, hgval, hBcard⟩ := children_approx β t ht hq2 cs ih
      obtain ⟨P, hP, hPe⟩ := or_approx (F := F) (q := q) (t := t) g
        (fun i x => (cs.get i).eval q (ext β x)) hgdeg B hgval
        (fun x => (Circuit.cor cs).eval q (ext β x))
        (fun x => by
          show (Circuit.cor cs).eval q (ext β x) = true ↔ ∃ i, (cs.get i).eval q (ext β x) = true
          rw [Circuit.eval_cor]; exact list_any_iff cs _)
      refine ⟨P, ?_, ?_⟩
      · rw [Circuit.depth_cor, pow_succ, mul_comm ((t * (q - 1)) ^ _) (t * (q - 1))]
        exact hP
      · rw [Circuit.size_cor, add_mul, one_mul]
        exact le_trans hPe (Nat.add_le_add_right hBcard _)
  | hand cs ih =>
      obtain ⟨g, B, hgdeg, hgval, hBcard⟩ := children_approx β t ht hq2 cs ih
      obtain ⟨Q, hQ, hQe⟩ := or_approx (F := F) (q := q) (t := t) (fun i => 1 - g i)
        (fun i x => !((cs.get i).eval q (ext β x)))
        (fun i => Submodule.sub_mem _ one_mem_Deg (hgdeg i)) B
        (fun x hx i => by
          show (1 : Cube n → F) x - g i x = bitv F (!((cs.get i).eval q (ext β x)))
          rw [bitv_not, hgval x hx i]
          rfl)
        (fun x => !((Circuit.cand cs).eval q (ext β x)))
        (fun x => by
          show ((!((Circuit.cand cs).eval q (ext β x))) = true) ↔
            ∃ i, ((!((cs.get i).eval q (ext β x))) = true)
          rw [Circuit.eval_cand]
          constructor
          · intro h
            have h' : ¬ ((cs.map (fun c => c.eval q (ext β x))).all id = true) := by
              simpa using h
            rw [list_all_iff] at h'
            push_neg at h'
            obtain ⟨i, hi⟩ := h'
            exact ⟨i, by simpa using hi⟩
          · rintro ⟨i, hi⟩
            have : ¬ ((cs.map (fun c => c.eval q (ext β x))).all id = true) := by
              rw [list_all_iff]
              push_neg
              exact ⟨i, by simpa using hi⟩
            simpa using this)
      refine ⟨1 - Q, ?_, ?_⟩
      · rw [Circuit.depth_cand, pow_succ, mul_comm ((t * (q - 1)) ^ _) (t * (q - 1))]
        exact Submodule.sub_mem _ one_mem_Deg hQ
      · have hfun : (fun x : Cube n => (Circuit.cand cs).eval q (ext β x))
            = fun x => !(!((Circuit.cand cs).eval q (ext β x))) := by funext x; simp
        rw [hfun, errSet_one_sub]
        rw [Circuit.size_cand, add_mul, one_mul]
        exact le_trans hQe (Nat.add_le_add_right hBcard _)
  | hmod cs ih =>
      obtain ⟨g, B, hgdeg, hgval, hBcard⟩ := children_approx β t ht hq2 cs ih
      refine ⟨1 - (∑ i : Fin cs.length, g i) ^ (q - 1), ?_, ?_⟩
      · rw [Circuit.depth_cmod, pow_succ, mul_comm ((t * (q - 1)) ^ _) (t * (q - 1))]
        refine Submodule.sub_mem _ one_mem_Deg ?_
        refine mem_Deg_of_le (pow_mem_Deg (Submodule.sum_mem _ fun i _ => hgdeg i)) ?_
        exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by omega))
      · have hsub : errSet (1 - (∑ i : Fin cs.length, g i) ^ (q - 1))
            (fun x => (Circuit.cmod cs).eval q (ext β x)) ⊆ B := by
          intro x hx
          by_contra hxB
          refine (mem_errSet.1 hx) ?_
          have hval : (∑ i : Fin cs.length, g i) x
              = ((((cs.map (fun c => c.eval q (ext β x))).count true : ℕ)) : F) := by
            rw [Finset.sum_apply]
            rw [list_count_map]
            push_cast
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hgval x hxB i]
            cases h : (cs.get i).eval q (ext β x) <;> simp
          simp only [Pi.sub_apply, Pi.one_apply, Pi.pow_apply, hval]
          rw [natCast_pow_q F q, Circuit.eval_cmod]
          by_cases hd : q ∣ (cs.map (fun c => c.eval q (ext β x))).count true
          · rw [if_pos hd, sub_zero,
              show decide ((cs.map (fun c => c.eval q (ext β x))).count true % q = 0) = true from
                by simp [Nat.dvd_iff_mod_eq_zero.mp hd]]
            rfl
          · rw [if_neg hd, sub_self,
              show decide ((cs.map (fun c => c.eval q (ext β x))).count true % q = 0) = false from
                by simpa using fun hc => hd (Nat.dvd_iff_mod_eq_zero.mpr hc)]
            rfl
        calc 2 ^ t * #(errSet (1 - (∑ i : Fin cs.length, g i) ^ (q - 1))
              (fun x => (Circuit.cmod cs).eval q (ext β x)))
            ≤ 2 ^ t * #B := Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
          _ ≤ (cs.map Circuit.size).sum * 2 ^ n := hBcard
          _ ≤ (Circuit.cmod cs).size * 2 ^ n := by
              rw [Circuit.size_cmod, add_mul, one_mul]; exact Nat.le_add_right _ _

end CS

import RequestProject.Deg
import RequestProject.Binomial

/-!
# Smolensky's dimension argument

If, on a set `A` of points of the cube `{0,1}ⁿ` (`n = 2m`), the function
`x ↦ ζ^(x₁+⋯+xₙ)` agrees with a polynomial of degree `D` (`ζ` a `p`-th root of unity), then
every function on `A` is the restriction of a polynomial of degree at most `m + D`, whence
`#A ≤ ∑_{i ≤ m+D} C(n,i)`.
-/

namespace CS

open Finset

variable {F : Type*} [Field F] {n : ℕ}

/-- `ζ ^ (x i)`, as a degree one function of `x`. -/
