import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem gpoly_mem_Deg (F : Type*) [Field F] (C : Circuit n) {q t : ℕ} (hq : 2 ≤ q)
    (ht : 1 ≤ t) (ρ : Rand C t) (i : Fin C.size) :
    gpoly F C q t ρ i ∈ Deg F n (((q - 1) * t) ^ (C.gdepth i)) := by
  have hb : 1 ≤ (q - 1) * t := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have H : ∀ N : ℕ, ∀ i : Fin C.size, i.val < N →
      gpoly F C q t ρ i ∈ Deg F n (((q - 1) * t) ^ (C.gdepth i)) := by
    intro N
    induction N with
    | zero => intro i hi; omega
    | succ N ih =>
      intro i hi
      have hchild : ∀ j : Fin i.val, (C.up i j).val < N := by
        intro j; have := j.isLt; simp only [Circuit.up]; omega
      rw [gpoly, gdepth]
      match hg : C.gate i with
      | .inp j =>
          simp only []
          exact mono_mem_Deg (by simp)
      | .cst b =>
          simp only []
          exact Deg_const_mem _
      | .notg j =>
          simp only []
          exact Submodule.sub_mem _ Deg_one_mem (ih (C.up i j) (hchild j))
      | .org S =>
          simp only []
          set D := S.sup (fun j => C.gdepth (C.up i j)) with hD
          have hchildD : ∀ j ∈ S, gpoly F C q t ρ (C.up i j) ∈ Deg F n (((q-1)*t)^D) :=
            fun j hj => mem_Deg_of_le (ih (C.up i j) (hchild j))
              (Nat.pow_le_pow_right hb (Finset.le_sup (f := fun j => C.gdepth (C.up i j)) hj))
          have hterm : ∀ k : Fin t,
              (1 - (∑ j ∈ S.filter (fun j => ρ i k (C.up i j) = true),
                gpoly F C q t ρ (C.up i j)) ^ (q-1)) ∈ Deg F n ((q-1) * ((q-1)*t)^D) :=
            fun k => Submodule.sub_mem _ Deg_one_mem
              (Deg_pow (Deg_sum (fun j hj => hchildD j (Finset.mem_filter.1 hj).1)))
          have hprod := Deg_prod (s := (univ : Finset (Fin t))) (fun k _ => hterm k)
          have hEq : (univ : Finset (Fin t)).card * ((q-1) * ((q-1)*t)^D) = ((q-1)*t)^(1+D) := by
            rw [Finset.card_univ, Fintype.card_fin, pow_add, pow_one]; ring
          rw [hEq] at hprod
          exact Submodule.sub_mem _ Deg_one_mem hprod
      | .andg S =>
          simp only []
          set D := S.sup (fun j => C.gdepth (C.up i j)) with hD
          have hchildD : ∀ j ∈ S, (1 - gpoly F C q t ρ (C.up i j)) ∈ Deg F n (((q-1)*t)^D) :=
            fun j hj => Submodule.sub_mem _ Deg_one_mem (mem_Deg_of_le (ih (C.up i j) (hchild j))
              (Nat.pow_le_pow_right hb (Finset.le_sup (f := fun j => C.gdepth (C.up i j)) hj)))
          have hterm : ∀ k : Fin t,
              (1 - (∑ j ∈ S.filter (fun j => ρ i k (C.up i j) = true),
                (1 - gpoly F C q t ρ (C.up i j))) ^ (q-1)) ∈ Deg F n ((q-1) * ((q-1)*t)^D) :=
            fun k => Submodule.sub_mem _ Deg_one_mem
              (Deg_pow (Deg_sum (fun j hj => hchildD j (Finset.mem_filter.1 hj).1)))
          have hprod := Deg_prod (s := (univ : Finset (Fin t))) (fun k _ => hterm k)
          have hEq : (univ : Finset (Fin t)).card * ((q-1) * ((q-1)*t)^D) = ((q-1)*t)^(1+D) := by
            rw [Finset.card_univ, Fintype.card_fin, pow_add, pow_one]; ring
          rw [hEq] at hprod
          exact hprod
      | .modg L =>
          simp only []
          set M := (L.map (fun j => C.gdepth (C.up i j))).foldr max 0 with hM
          have hsum : ((L.map (fun j => gpoly F C q t ρ (C.up i j))).sum)
              ∈ Deg F n (((q-1)*t)^M) := by
            refine Deg_list_sum _ ?_
            intro f hf
            obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf
            exact mem_Deg_of_le (ih (C.up i j) (hchild j))
              (Nat.pow_le_pow_right hb (list_foldr_max_le L (fun j => C.gdepth (C.up i j)) j hj))
          refine mem_Deg_of_le (Deg_pow hsum) ?_
          rw [pow_add, pow_one]
          exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ ht)
  exact H (i.val + 1) i (Nat.lt_succ_self _)

/-- The randomized polynomial is correct at gate `i` on input `x`. -/
