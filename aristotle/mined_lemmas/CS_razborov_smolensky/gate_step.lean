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
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module docstring, so the header above is
-- written as a plain block comment and repeated verbatim as a module docstring below.)

import RequestProject.RS.CircuitApprox
import RequestProject.RS.Smolensky
import RequestProject.RS.Binomial
import RequestProject.RS.Aux
import RequestProject.RS.Sanity

/-!
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Razborov–Smolensky theorem: for distinct primes `p` and `q`, the Boolean function `MOD p`
(which tests whether the number of `1`s in the input is divisible by `p`) is not computed by any
family of constant-depth, polynomial-size circuits with unbounded fan-in AND, OR, NOT and
`MOD q` gates, i.e. `MOD p ∉ AC⁰[q]`.

The proof combines
* `CS.RS.Circuit.exists_approx`: every `AC⁰[q]` circuit is approximated, on all but a small
  fraction of the inputs, by a low-degree function over a field of characteristic `q`;
* `CS.RS.smolensky_bound`: a low-degree function can agree with `x ↦ ζ^(weight x)` (for `ζ` a
  primitive `p`-th root of unity) only on a set of inputs of size at most
  `∑_{i ≤ n/2 + D} C(n,i)`;
* `CS.RS.modq_mem_AC0q`: a non-vacuity check, exhibiting `MOD q` itself as a depth-one,
  linear-size circuit family of this kind;
* binomial estimates showing that this is less than the number of inputs left over by the
  approximation step.
-/

namespace CS

open Finset CS.RS

/-- Shifting the weight by `(p - r) % p` detects the residue `r` modulo `p`. -/

theorem gate_step (q : ℕ) [Fact q.Prime] {K : Type*} [Field K] [CharP K q] {n : ℕ}
    (C : Circuit n) (l : ℕ) (hl : 1 ≤ l) (i : ℕ) (hi : i < C.size) (f : ℕ → Fn K n)
    (hdeg : ∀ j, j < i → f j ∈ Deg K n (((q-1)*l)^(C.dep j)))
    (A : Finset (Cube n)) (hA : ∀ x ∈ A, ∀ j, j < i → f j x = ind K (C.evalAt q x j)) :
    ∃ g : Fn K n, g ∈ Deg K n (((q-1)*l)^(C.dep i)) ∧
      2^l * (A.filter (fun x => g x ≠ ind K (C.evalAt q x i))).card ≤ 2^n := by
  classical
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  set Aq := (q-1)*l with hAqdef
  have hAq1 : 1 ≤ Aq := by
    rw [hAqdef]
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hchild : ∀ j ∈ (C.gates i).children, j < i := C.acyclic i hi
  have hchild_dep : ∀ j ∈ (C.gates i).children, C.dep j < C.dep i :=
    fun j hj => C.dep_child_lt hj (hchild j hj)
  set E := (if (C.gates i).children = [] then 0 else Aq^(C.dep i - 1)) with hEdef
  have hmemE : ∀ j ∈ (C.gates i).children, f j ∈ Deg K n E := by
    intro j hj
    have hne : (C.gates i).children ≠ [] := by
      intro h; rw [h] at hj; simp at hj
    rw [hEdef, if_neg hne]
    exact (Deg_le (Nat.pow_le_pow_right hAq1
      (by have := hchild_dep j hj; omega))) (hdeg j (hchild j hj))
  have hEbound : l * ((q-1) * E) ≤ Aq^(C.dep i) := by
    by_cases hne : (C.gates i).children = []
    · rw [hEdef, if_pos hne]; simp
    · obtain ⟨j, hj⟩ : ∃ j, j ∈ (C.gates i).children := by
        cases h : (C.gates i).children with
        | nil => exact absurd h hne
        | cons a t => exact ⟨a, by simp⟩
      have hdp : 1 ≤ C.dep i := by have := hchild_dep j hj; omega
      rw [hEdef, if_neg hne]
      have : l * ((q-1) * Aq^(C.dep i - 1)) = Aq^(C.dep i - 1 + 1) := by
        rw [pow_succ, hAqdef]; ring
      rw [this]
      exact le_of_eq (by congr 1; omega)
  have hEbound2 : (q-1) * E ≤ Aq^(C.dep i) := by
    refine le_trans ?_ hEbound
    calc (q-1) * E = 1 * ((q-1) * E) := by ring
      _ ≤ l * ((q-1) * E) := Nat.mul_le_mul_right _ hl
  have hEbound3 : E ≤ Aq^(C.dep i) := by
    refine le_trans ?_ hEbound2
    calc E = 1 * E := by ring
      _ ≤ (q-1) * E := Nat.mul_le_mul_right _ (by omega)
  -- a perfectly correct approximation has no error at all
  have hexact : ∀ g : Fn K n, (∀ x ∈ A, g x = ind K (C.evalAt q x i)) →
      2^l * (A.filter (fun x => g x ≠ ind K (C.evalAt q x i))).card ≤ 2^n := by
    intro g hg
    have hemp : A.filter (fun x => g x ≠ ind K (C.evalAt q x i)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx
      simpa using hg x hx
    rw [hemp]
    simp
  -- the value function used inside gate `i`
  set v : Cube n → ℕ → Bool := fun x j => if _h : j < i then C.evalAt q x j else false with hvdef
  have heval : ∀ x : Cube n, C.evalAt q x i = Gate.value q (C.gates i) x (v x) := by
    intro x
    rw [C.evalAt_eq x i]
  have hv : ∀ x, ∀ j ∈ (C.gates i).children, v x j = C.evalAt q x j := by
    intro x j hj
    rw [hvdef]
    simp [hchild j hj]
  clear_value E
  rcases hgate : C.gates i with k | b | j | lst | lst | lst
  · -- input gate
    refine ⟨fun x => ind K (x k), ?_, ?_⟩
    · have hd0 : C.dep i = 0 := C.dep_eq_zero (by rw [hgate]; rfl)
      rw [hd0, pow_zero]
      exact coord_mem_Deg k
    · refine hexact _ (fun x _ => ?_)
      rw [heval x, hgate]
      rfl
  · -- constant gate
    refine ⟨fun _ => ind K b, ?_, ?_⟩
    · exact const_mem_Deg _ _
    · refine hexact _ (fun x _ => ?_)
      rw [heval x, hgate]
      rfl
  · -- negation gate
    have hjc : j ∈ (C.gates i).children := by rw [hgate]; simp [Gate.children]
    refine ⟨(1 : Fn K n) - f j, ?_, ?_⟩
    · refine Submodule.sub_mem _ (one_mem_Deg _) ?_
      exact (Deg_le (Nat.pow_le_pow_right hAq1 (le_of_lt (hchild_dep j hjc)))) (hdeg j (hchild j hjc))
    · refine hexact _ (fun x hx => ?_)
      rw [heval x, hgate]
      have : Gate.value q (Gate.neg j) x (v x) = !(C.evalAt q x j) := by
        simp [Gate.value, hv x j hjc]
      rw [this, ind_not]
      simp only [Pi.sub_apply, Pi.one_apply]
      rw [hA x hx j (hchild j hjc)]
  · -- conjunction gate
    have hlst : ∀ t : Fin lst.length, lst.get t ∈ (C.gates i).children := by
      intro t; rw [hgate]; exact List.get_mem lst t
    set u : Fin lst.length → Fn K n := fun t => (1 : Fn K n) - f (lst.get t) with hudef
    set bb : Fin lst.length → Cube n → Bool := fun t x => !(C.evalAt q x (lst.get t)) with hbbdef
    have hu : ∀ x ∈ A, ∀ t, u t x = ind K (bb t x) := by
      intro x hx t
      rw [hudef, hbbdef]
      simp only [Pi.sub_apply, Pi.one_apply]
      rw [ind_not, hA x hx (lst.get t) (hchild _ (hlst t))]
    obtain ⟨S, hS⟩ := or_approx (l := l) q u bb A hu
    refine ⟨(1 : Fn K n) - orPoly q S u, ?_, ?_⟩
    · refine Submodule.sub_mem _ (one_mem_Deg _) ?_
      refine (Deg_le hEbound) (orPoly_mem_Deg q S u ?_)
      intro t
      exact Submodule.sub_mem _ (one_mem_Deg _) (hmemE _ (hlst t))
    · -- the target values agree
      have htarget : ∀ x, ind K (C.evalAt q x i)
          = 1 - ind K (decide (∃ t, bb t x = true)) := by
        intro x
        rw [heval x, hgate]
        have hval : Gate.value q (Gate.conj lst) x (v x) = lst.all (v x) := rfl
        rw [hval]
        by_cases hall : lst.all (v x) = true
        · have hnex : ¬ ∃ t, bb t x = true := by
            rintro ⟨t, ht⟩
            rw [hbbdef] at ht
            simp only [Bool.not_eq_true'] at ht
            have hmem : v x (lst.get t) = true := by
              rw [List.all_eq_true] at hall
              exact hall _ (List.get_mem lst t)
            rw [hv x _ (hlst t)] at hmem
            rw [hmem] at ht
            exact absurd ht (by simp)
          rw [hall, decide_eq_false hnex]
          simp [ind]
        · simp only [Bool.not_eq_true] at hall
          have hex : ∃ t, bb t x = true := by
            rw [List.all_eq_false] at hall
            obtain ⟨a, ha, hfa⟩ := hall
            obtain ⟨t, ht⟩ := List.mem_iff_get.1 ha
            refine ⟨t, ?_⟩
            rw [hbbdef]
            simp only
            rw [← hv x _ (hlst t), ht]
            simp [hfa]
          rw [hall, decide_eq_true hex]
          simp [ind]
      have hsets : (A.filter (fun x => ((1 : Fn K n) - orPoly q S u) x
            ≠ ind K (C.evalAt q x i)))
          = A.filter (fun x => orPoly q S u x ≠ ind K (decide (∃ t, bb t x = true))) := by
        refine Finset.filter_congr (fun x _ => ?_)
        rw [htarget x]
        simp only [Pi.sub_apply, Pi.one_apply, ne_eq, sub_right_inj]
      rw [hsets]
      exact hS
  · -- disjunction gate
    have hlst : ∀ t : Fin lst.length, lst.get t ∈ (C.gates i).children := by
      intro t; rw [hgate]; exact List.get_mem lst t
    set u : Fin lst.length → Fn K n := fun t => f (lst.get t) with hudef
    set bb : Fin lst.length → Cube n → Bool := fun t x => C.evalAt q x (lst.get t) with hbbdef
    have hu : ∀ x ∈ A, ∀ t, u t x = ind K (bb t x) := by
      intro x hx t
      rw [hudef, hbbdef]
      exact hA x hx (lst.get t) (hchild _ (hlst t))
    obtain ⟨S, hS⟩ := or_approx (l := l) q u bb A hu
    refine ⟨orPoly q S u, ?_, ?_⟩
    · refine (Deg_le hEbound) (orPoly_mem_Deg q S u ?_)
      intro t
      exact hmemE _ (hlst t)
    · have htarget : ∀ x, ind K (C.evalAt q x i) = ind K (decide (∃ t, bb t x = true)) := by
        intro x
        rw [heval x, hgate]
        have hval : Gate.value q (Gate.disj lst) x (v x) = lst.any (v x) := rfl
        rw [hval]
        by_cases hany : lst.any (v x) = true
        · have hex : ∃ t, bb t x = true := by
            rw [List.any_eq_true] at hany
            obtain ⟨a, ha, hfa⟩ := hany
            obtain ⟨t, ht⟩ := List.mem_iff_get.1 ha
            refine ⟨t, ?_⟩
            rw [hbbdef]
            simp only
            rw [← hv x _ (hlst t), ht]
            exact hfa
          rw [hany, decide_eq_true hex]
        · simp only [Bool.not_eq_true] at hany
          have hnex : ¬ ∃ t, bb t x = true := by
            rintro ⟨t, ht⟩
            rw [hbbdef] at ht
            simp only at ht
            rw [← hv x _ (hlst t)] at ht
            rw [List.any_eq_false] at hany
            exact absurd ht (by simpa using hany _ (List.get_mem lst t))
          rw [hany, decide_eq_false hnex]
      have hsets : (A.filter (fun x => orPoly q S u x ≠ ind K (C.evalAt q x i)))
          = A.filter (fun x => orPoly q S u x ≠ ind K (decide (∃ t, bb t x = true))) := by
        refine Finset.filter_congr (fun x _ => ?_)
        rw [htarget x]
      rw [hsets]
      exact hS
  · -- MOD q gate
    have hlst : ∀ j ∈ lst, j ∈ (C.gates i).children := by
      intro j hj; rw [hgate]; exact hj
    refine ⟨fun x => ((lst.map (fun j => f j x)).sum)^(q-1), ?_, ?_⟩
    · have hsum : (fun x => (lst.map (fun j => f j x)).sum) ∈ Deg K n E :=
        listSum_mem_Deg lst f E (fun j hj => hmemE j (hlst j hj))
      have hpow := pow_mem_Deg (q-1) hsum
      have hrw : (fun x => (lst.map (fun j => f j x)).sum)^(q-1)
          = (fun x => ((lst.map (fun j => f j x)).sum)^(q-1)) := by
        funext x; rw [Pi.pow_apply]
      rw [hrw] at hpow
      exact (Deg_le hEbound2) hpow
    · refine hexact _ (fun x hx => ?_)
      have hmapeq : (lst.map (fun j => f j x)) = lst.map (fun j => ind K (C.evalAt q x j)) := by
        refine List.map_congr_left (fun j hj => ?_)
        exact hA x hx j (hchild j (hlst j hj))
      rw [hmapeq, list_map_ind_sum, natCast_pow_q_sub_one K q]
      rw [heval x, hgate]
      have hval : Gate.value q (Gate.modq lst) x (v x)
          = decide (¬ q ∣ (lst.filter (v x)).length) := rfl
      rw [hval]
      have hfil : lst.filter (v x) = lst.filter (fun j => C.evalAt q x j) := by
        refine List.filter_congr (fun j hj => ?_)
        rw [hv x j (hlst j hj)]
      rw [hfil]
      by_cases hd : q ∣ (lst.filter (fun j => C.evalAt q x j)).length
      · rw [if_pos hd, decide_eq_false (by simpa using hd)]
        rfl
      · rw [if_neg hd, decide_eq_true (by simpa using hd)]
        rfl

/-- Gate-by-gate approximation: after processing the first `i` gates there are approximating
functions of the right degree whose total error set has size at most `i * 2^n / 2^ℓ`. -/
