import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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

namespace QI

/-! ## The Boolean cube as an `𝔽₂`-vector space -/

/-- `n`-bit strings, viewed as the elementary abelian 2-group `(ℤ/2)ⁿ`;
addition is bitwise XOR. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2


lemma classical_lower_bound {n d : ℕ} (T : DTree n d) (hn : 1 ≤ n) (hT : Solves T) :
    2 ^ (n / 2) ≤ d := by
  by_contra hcon
  push_neg at hcon
  set Q : Finset (V n) := T.queries (id : V n → V n) with hQdef
  have hQcard : Q.card ≤ d := DTree.card_queries_le T id
  set bad : Finset (V n) := insert 0 (Q.offDiag.image (fun p => p.1 + p.2)) with hbaddef
  -- the set of shifts excluded by the queries is too small to exhaust the cube
  have hmm : 2 ^ (n / 2) * 2 ^ (n / 2) ≤ 2 ^ n := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have htwo : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hbadcard : bad.card < 2 ^ n := by
    have h1 : bad.card ≤ 1 + (Q.card * Q.card - Q.card) := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      have h2 := Finset.card_image_le (s := Q.offDiag) (f := fun p : V n × V n => p.1 + p.2)
      rw [Finset.offDiag_card] at h2
      omega
    rcases Nat.eq_zero_or_pos Q.card with h0 | h0
    · rw [h0] at h1
      simp at h1
      omega
    · have hle : Q.card * Q.card ≤ d * d := Nat.mul_le_mul hQcard hQcard
      have hlt : d * d < 2 ^ (n / 2) * 2 ^ (n / 2) := Nat.mul_lt_mul'' hcon hcon
      have hself : Q.card ≤ Q.card * Q.card := Nat.le_mul_of_pos_left _ h0
      omega
  obtain ⟨s, hsbad⟩ : ∃ s : V n, s ∉ bad := by
    by_contra hall
    push_neg at hall
    have hsub : (Finset.univ : Finset (V n)) ⊆ bad := fun x _ => hall x
    have := Finset.card_le_card hsub
    have hcard : (Finset.univ : Finset (V n)).card = 2 ^ n := by simp
    omega
  have hs0 : s ≠ 0 := by
    intro h
    exact hsbad (by rw [hbaddef, h]; exact Finset.mem_insert_self _ _)
  have hQfree : ∀ a ∈ Q, a + s ∉ Q := by
    intro a ha hb
    refine hsbad ?_
    have hne : a ≠ a + s := fun h => hs0 (left_eq_add.mp h)
    have hmem : (a, a + s) ∈ Q.offDiag := Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩
    have hsum : a + (a + s) = s := by
      rw [← add_assoc, add_self_cube, zero_add]
    rw [hbaddef]
    refine Finset.mem_insert_of_mem ?_
    exact Finset.mem_image.mpr ⟨(a, a + s), hmem, hsum⟩
  obtain ⟨i0, hi0⟩ : ∃ i : Fin n, s i = 1 := by
    by_contra hcon2
    push_neg at hcon2
    refine hs0 (funext fun i => ?_)
    rcases zmod2_cases (s i) with h | h
    · exact h
    · exact absurd h (hcon2 i)
  have hrun : T.run (adversaryOracle Q s i0) = T.run id :=
    DTree.run_congr T id (adversaryOracle Q s i0)
      (fun x hx => adversaryOracle_mem Q s i0 hx)
  rw [hT.1 id Function.injective_id,
    hT.2 (adversaryOracle Q s i0) s hs0 (adversaryOracle_isShift Q s i0 hi0 hQfree)] at hrun
  exact Bool.noConfusion hrun

/-- **Non-vacuity of the classical lower bound.**  Simon's problem really is solvable by a
deterministic query algorithm: here, for `n = 1`, by querying both points of the cube and
comparing the answers. -/
