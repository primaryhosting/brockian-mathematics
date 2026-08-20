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

lemma or_approx (q : ℕ) [Fact q.Prime] {K : Type*} [Field K] [CharP K q] {n m l : ℕ}
    (u : Fin m → Fn K n) (b : Fin m → Cube n → Bool) (A : Finset (Cube n))
    (hu : ∀ x ∈ A, ∀ t, u t x = ind K (b t x)) :
    ∃ S : Fin l → Finset (Fin m),
      2^l * (A.filter (fun x => orPoly q S u x ≠ ind K (decide (∃ t, b t x = true)))).card
        ≤ 2^n := by
  classical
  set Om := (univ : Finset (Fin l → Finset (Fin m))) with hOm
  set N := Fintype.card (Fin l → Finset (Fin m)) with hN
  -- for each good input, few seeds are bad
  have hx : ∀ x ∈ A,
      2^l * (Om.filter (fun S => orPoly q S u x ≠ ind K (decide (∃ t, b t x = true)))).card ≤ N := by
    intro x hxA
    by_cases hex : ∃ t, b t x = true
    · obtain ⟨t₀, ht₀⟩ := hex
      have h1 : u t₀ x ≠ 0 := by
        rw [hu x hxA t₀, ht₀]; simp [ind]
      have hsub : (Om.filter (fun S => orPoly q S u x ≠ ind K (decide (∃ t, b t x = true))))
          ⊆ Om.filter (fun S => ∀ k, ∑ t ∈ S k, u t x = 0) := by
        intro S hS
        rw [mem_filter] at hS ⊢
        refine ⟨hS.1, ?_⟩
        intro k
        by_contra hne
        -- if some sum is nonzero, the corresponding factor vanishes, so orPoly = 1
        have hc : ∑ t ∈ S k, u t x = (((S k).filter (fun t => b t x = true)).card : K) := by
          rw [show (fun t => u t x) = (fun t => ind K (b t x)) from funext (fun t => hu x hxA t)]
          exact sum_ind_eq_card _ _
        have hnd : ¬ q ∣ ((S k).filter (fun t => b t x = true)).card := by
          intro hd
          apply hne
          rw [hc, (CharP.cast_eq_zero_iff K q _).2 hd]
        have hfac : (1 : K) - (∑ t ∈ S k, u t x)^(q-1) = 0 := by
          rw [hc, natCast_pow_q_sub_one K q, if_neg hnd, sub_self]
        have hprod : ∏ k : Fin l, (1 - (∑ t ∈ S k, u t x)^(q-1)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) hfac
        have : orPoly q S u x = ind K (decide (∃ t, b t x = true)) := by
          simp only [orPoly, hprod, sub_zero]
          rw [decide_eq_true (⟨t₀, ht₀⟩ : ∃ t, b t x = true)]
          simp [ind]
        exact hS.2 this
      calc 2^l * (Om.filter (fun S => orPoly q S u x ≠ ind K (decide (∃ t, b t x = true)))).card
          ≤ 2^l * (Om.filter (fun S => ∀ k, ∑ t ∈ S k, u t x = 0)).card := by
            exact Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
        _ ≤ N := card_badseed_le (fun t => u t x) t₀ h1
    · -- all children are false: the approximation is exact
      have hz : ∀ t, u t x = 0 := by
        intro t
        rw [hu x hxA t]
        cases hbt : b t x
        · simp [ind]
        · exact absurd ⟨t, hbt⟩ hex
      have hempty : (Om.filter (fun S => orPoly q S u x ≠ ind K (decide (∃ t, b t x = true))))
          = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro S _
        simp only [not_not]
        have hsum : ∀ k, ∑ t ∈ S k, u t x = 0 := by
          intro k; exact Finset.sum_eq_zero (fun t _ => hz t)
        have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
        have : ∀ k : Fin l, (1 : K) - (∑ t ∈ S k, u t x)^(q-1) = 1 := by
          intro k; rw [hsum k, zero_pow (by omega), sub_zero]
        simp only [orPoly, this, Finset.prod_const_one, sub_self]
        rw [decide_eq_false hex]
        simp [ind]
      rw [hempty]
      simp
  -- sum over all seeds
  have hswap : ∑ S ∈ Om, (A.filter (fun x => orPoly q S u x
        ≠ ind K (decide (∃ t, b t x = true)))).card
      = ∑ x ∈ A, (Om.filter (fun S => orPoly q S u x
        ≠ ind K (decide (∃ t, b t x = true)))).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hAcard : A.card ≤ 2^n := by
    have h1 : A.card ≤ Fintype.card (Cube n) := Finset.card_le_univ A
    simpa [Fintype.card_fun] using h1
  have htotal : 2^l * ∑ S ∈ Om, (A.filter (fun x => orPoly q S u x
      ≠ ind K (decide (∃ t, b t x = true)))).card ≤ N * 2^n := by
    rw [hswap, Finset.mul_sum]
    calc ∑ x ∈ A, 2^l * (Om.filter (fun S => orPoly q S u x
            ≠ ind K (decide (∃ t, b t x = true)))).card
        ≤ ∑ _x ∈ A, N := Finset.sum_le_sum hx
      _ = A.card * N := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2^n * N := Nat.mul_le_mul_right _ hAcard
      _ = N * 2^n := mul_comm _ _
  have hNe : Om.Nonempty := by
    refine ⟨fun _ => ∅, Finset.mem_univ _⟩
  have hsumle : ∑ S ∈ Om, (2^l * (A.filter (fun x => orPoly q S u x
      ≠ ind K (decide (∃ t, b t x = true)))).card) ≤ ∑ _S ∈ Om, 2^n := by
    rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul, hOm]
    have : (univ : Finset (Fin l → Finset (Fin m))).card = N := by
      rw [hN, Finset.card_univ]
    rw [this]
    exact htotal
  obtain ⟨S, _, hS⟩ := Finset.exists_le_of_sum_le hNe hsumle
  exact ⟨S, hS⟩

/-- A gate with no children has depth zero. -/
