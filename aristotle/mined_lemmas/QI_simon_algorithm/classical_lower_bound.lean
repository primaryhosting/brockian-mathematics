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
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace QI

/-! ## Basic setup: the group `(ZMod 2)^n` -/

/-- The domain of Simon's problem: bit strings of length `n`, viewed as the
elementary abelian group `(ZMod 2)^n` under bitwise XOR (= addition). -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


theorem classical_lower_bound (hn : 2 ≤ n) (T : DTree n) (d : ℕ) (hd : DTree.DepthLE T d)
    (hcorrect : ∀ (s : Vec n) (f : Vec n → ℕ), IsSimon s f → T.run f = s) :
    2 ^ ((n - 1) / 2) ≤ d := by
  classical
  by_contra hlt
  push_neg at hlt
  set S : Finset (Vec n) := T.queries enc with hSdef
  have hcard : S.card ≤ d := DTree.card_queries_le hd enc
  set D : Finset (Vec n) :=
    insert 0 (insert (T.run enc) ((S ×ˢ S).image (fun p => p.1 + p.2))) with hD
  have hDcard : D.card ≤ d * d + 2 := by
    have h1 : ((S ×ˢ S).image (fun p : Vec n × Vec n => p.1 + p.2)).card ≤ d * d := by
      refine le_trans Finset.card_image_le ?_
      rw [Finset.card_product]
      exact Nat.mul_le_mul hcard hcard
    calc D.card ≤ (insert (T.run enc) ((S ×ˢ S).image (fun p => p.1 + p.2))).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (((S ×ˢ S).image (fun p => p.1 + p.2)).card + 1) + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ d * d + 2 := by omega
  have hlt2 : d * d + 2 < 2 ^ n := by
    have h1 : d + 1 ≤ 2 ^ ((n - 1) / 2) := hlt
    have h3 : (2 : ℕ) ^ ((n - 1) / 2) * 2 ^ ((n - 1) / 2) ≤ 2 ^ (n - 1) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h5 : (2 : ℕ) ^ 1 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h6 : (d + 1) * (d + 1) ≤ 2 ^ (n - 1) := le_trans (Nat.mul_le_mul h1 h1) h3
    rw [h4]
    nlinarith [h6, h5]
  have hDlt : D.card < Fintype.card (Vec n) := by
    rw [card_vec]; omega
  obtain ⟨s, hs⟩ : ∃ s : Vec n, s ∉ D := by
    by_contra hc
    push_neg at hc
    have hu : D = Finset.univ := Finset.eq_univ_of_forall hc
    rw [hu, Finset.card_univ] at hDlt
    exact lt_irrefl _ hDlt
  have hs0 : s ≠ 0 := by
    intro e; exact hs (by rw [e, hD]; exact Finset.mem_insert_self _ _)
  have hsout : s ≠ T.run enc := by
    intro e
    exact hs (by rw [e, hD]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hSsum : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ≠ s := by
    intro x hx y hy _ e
    refine hs ?_
    rw [hD]
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
    exact Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, e⟩
  have hsimon : IsSimon s (advFn S s) := advFn_isSimon hs0 hSsum
  have hagree : ∀ x ∈ T.queries enc, enc x = advFn S s x := by
    intro x hx
    exact (advFn_agree (S := S) (s := s) (hSdef ▸ hx)).symm
  have hrun : T.run (advFn S s) = T.run enc := (T.run_congr enc (advFn S s) hagree).1
  exact hsout (by rw [← hcorrect s _ hsimon, hrun])

/-! ## Main theorem -/

/-- **Simon's problem.**

*Quantum upper bound*: for every Simon function `f` with secret `s` (over `n ≥ 2`
bits) there are `n - 1` outcomes `y`, each of which occurs with nonzero amplitude in
the state produced by a single quantum query (`amp`), such that `s` is the unique
nonzero vector orthogonal to all of them.  So `O(n)` quantum queries determine `s`.

*Classical lower bound*: every deterministic classical query algorithm (decision
tree) that outputs the secret of every Simon function must make at least
`2 ^ ((n-1)/2) = Ω(2^{n/2})` queries. -/
