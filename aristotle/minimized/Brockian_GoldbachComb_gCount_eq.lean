/-
  Brockian/GoldbachComb.lean — THE GOLDBACH COMB CAMPAIGN (July 30).

  The exact local covariance kernel behind the 3|k autocorrelation comb
  of the Goldbach residual (Volume II, page XVI; Tomography §4).

  Chain: local count g_p(c) = p−2+[c=0]  →  centered spike 1_{c=0}−1/p
  →  two-case covariance  →  CRT product over squarefree wheels  →
  convergent global kernel K(h) with  K(h)−1 > 0 ⟺ 3 ∣ h  (the p=3
  factor 9/8 vs 15/16 dominates all higher primes combined).

  Empirical status (this program, recorded): kernel verified exactly at
  p = 3,5,7,11; global values K−1 = +0.1195 / −0.0671; transfer pilot
  against the measured 50-lag ACF: one fitted scale β ≈ 0.41, held-out
  sign agreement 25/25, correlation r = 0.996. The TRANSFER conjecture
  is named at the end and never claimed.

  Charter as Core.lean; each unproved declaration was supplied as a target.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.GoldbachComb

open Finset

/-- The local Goldbach count: ordered pairs of nonzero residues summing
to c. -/

def gCount (p : ℕ) [NeZero p] (c : ZMod p) : ℕ :=
  (univ.filter (fun xy : ZMod p × ZMod p =>
    xy.1 ≠ 0 ∧ xy.2 ≠ 0 ∧ xy.1 + xy.2 = c)).card

/-- GC-1 (target): the exact local count, g_p(c) = p−2+[c=0] for prime
p (p−1 pairs at c = 0; p−2 otherwise). -/

theorem gCount_eq (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    gCount p c = if c = 0 then p - 1 else p - 2 := by
  split_ifs with hc
  · -- Case c = 0
    subst hc
    simp [gCount]
    have hmap : (univ.filter (fun xy : ZMod p × ZMod p => ¬xy.1 = 0 ∧ ¬xy.2 = 0 ∧ xy.1 + xy.2 = 0)) =
      (univ.filter (fun a : ZMod p => ¬a = 0)).image (fun a => (a, -a)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro ⟨ha, hb, hsum⟩
        refine ⟨a, ha, ?_⟩
        simp [show b = -a from eq_neg_of_add_eq_zero_right hsum]
      · intro ⟨a', ha', hpair⟩
        rcases hpair with ⟨rfl, rfl⟩
        exact ⟨ha', neg_ne_zero.mpr ha', by simp⟩
    rw [hmap]
    rw [Finset.card_image_of_injective]
    · have : (univ.filter (fun a : ZMod p => ¬a = 0)) = Finset.univ.erase 0 := by
        ext x; simp [Finset.mem_erase]
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
      rw [ZMod.card]
    · exact fun a b hab => by simp at hab; exact hab
  · -- Case c ≠ 0
    simp [gCount]
    have hmap : (univ.filter (fun xy : ZMod p × ZMod p => ¬xy.1 = 0 ∧ ¬xy.2 = 0 ∧ xy.1 + xy.2 = c)) =
      (univ.filter (fun a : ZMod p => ¬a = 0 ∧ ¬a = c)).image (fun a => (a, c - a)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro ⟨ha, hb, hsum⟩
        refine ⟨a, ⟨ha, ?_⟩, ?_⟩
        · intro hac
          rw [hac] at hsum
          rw [add_eq_left] at hsum
          exact hb hsum
        · simp [show b = c - a from by rw [← add_comm] at hsum; exact eq_sub_of_add_eq hsum]
      · intro ⟨a', ha', hpair⟩
        rcases hpair with ⟨rfl, rfl⟩
        refine ⟨ha'.1, ?_, by simp⟩
        intro hc'
        apply ha'.2
        rw [eq_comm]
        exact eq_of_sub_eq_zero hc'
    rw [hmap]
    rw [Finset.card_image_of_injective]
    · have hcard : (univ.filter (fun a : ZMod p => ¬a = 0 ∧ ¬a = c)) = 
        ((univ.erase 0).erase c) := by
        ext x
        simp [Finset.mem_erase]
        tauto
      rw [hcard, Finset.card_erase_of_mem, Finset.card_erase_of_mem]
      · rw [Finset.card_univ, ZMod.card]
        omega
      · simp
      · simp [Finset.mem_erase, hc]
    · exact fun a b hab => by simp at hab; exact hab

/-- GC-2 (target): the centered spike identity — over ℚ,
g_p(c) − (p−1)²/p = [c = 0] − 1/p. -/
