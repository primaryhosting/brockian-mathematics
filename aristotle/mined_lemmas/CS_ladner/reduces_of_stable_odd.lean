/-
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file formalizes Ladner's theorem: *if `P ≠ NP` then there are `NP`-intermediate
languages*, i.e. languages that are in `NP`, not in `P`, and not `NP`-complete.

The proof is Ladner's delayed ("lazy") diagonalization: one builds a nondecreasing "hole"
function `hole : ℕ → ℕ` and looks at the language

  `A = K ∩ { x | hole (bit length of x) is even }`,

where `K` is an `NP`-complete language.  While `hole` sits at an even value `2 i` the
construction searches, with a growing step budget, for an input on which the `i`-th
polynomial-time machine disagrees with `A`; while it sits at an odd value `2 j + 1` it
searches for an input witnessing that the `j`-th polynomial-time function fails to reduce
`K` to `A`.  Each time such a witness is found the hole function moves on to the next stage.

If `hole` were bounded it would be eventually constant, and then either `A` would be decided
by a polynomial-time machine while differing from `K` only on finitely many inputs (even
case), or `A` would be finite while `K` reduces to it (odd case); both put `K` in `P`,
contradicting `P ≠ NP`.  Hence `hole` is unbounded, and therefore no machine decides `A` and
no polynomial-time function reduces `K` to `A`; that is, `A` is `NP`-intermediate.

The classes `P` and `NP` are not available in Mathlib, so they are axiomatized here by the
structure `CS.World`, which collects exactly the properties of `P`, `NP`, polynomial-time
many-one reductions, machine enumerations and step-bounded simulations that the argument
uses.  Section "A model" builds an explicit `World`, so that the axiom system is consistent
(of course no `World` with `inP ≠ inNP` can be exhibited, since `P` vs `NP` is open).
-/

namespace CS

/-- A language is a Boolean predicate on `ℕ`; inputs (strings) are encoded as natural
numbers, and `Nat.size x` is the bit length of the input `x`. -/
abbrev Lang := ℕ → Bool

/-- The bit length of `x` is at most `x`. -/

lemma reduces_of_stable_odd (N : ℕ) (hstab : ∀ n, N ≤ n → F n = F N) (j : ℕ)
    (hj : F N = 2 * j + 1) : ∀ x, W.K x = ladnerLang W.K W.sim W.simR (W.R j x) := by
  have hwit : ∀ n, N ≤ n → witOdd W.K W.simR j F n = false := by
    intro n hn
    have h1 : F n = F N := hstab n hn
    have h2 : F (n + 1) = F N := hstab (n + 1) (by omega)
    have hod : ¬ Even (F n) := by
      rw [h1, hj]
      simp [parity_simps]
    have hrec := hole_succ_odd W.K W.sim W.simR hod
    rw [h1, hj] at hrec
    have hdiv : (2 * j + 1) / 2 = j := by omega
    rw [hdiv] at hrec
    by_cases hw : witOdd W.K W.simR j F n = true
    · rw [hw, if_pos rfl] at hrec
      rw [h2, hj] at hrec
      omega
    · simpa using hw
  intro x
  obtain ⟨t, ht⟩ := W.simR_halts j x
  set n := max (max N (x + 1)) (max t (W.R j x)) with hn
  have hsim : W.simR j x n = some (W.R j x) :=
    W.simR_mono j x t n _ (le_trans (le_max_left t (W.R j x)) (le_max_right _ _)) ht
  have hw := hwit n (le_trans (le_max_left N (x + 1)) (le_max_left _ _))
  have hxn : x < n := lt_of_lt_of_le (Nat.lt_succ_self x)
    (le_trans (le_max_right N (x + 1)) (le_max_left _ _))
  have hyn : W.R j x < n + 1 :=
    Nat.lt_succ_of_le (le_trans (le_max_right t (W.R j x)) (le_max_right _ _))
  by_contra hne
  have : witOdd W.K W.simR j F n = true := by
    simp only [witOdd, List.any_eq_true, List.mem_range]
    refine ⟨x, hxn, W.R j x, hyn, ?_⟩
    have hdd : ladnerLang W.K W.sim W.simR (W.R j x) = diag W.K F (W.R j x) := rfl
    rw [hdd] at hne
    rw [hsim]
    cases hb : W.K x <;> cases hd : diag W.K F (W.R j x) <;> simp [hb, hd] at hne ⊢
  rw [hw] at this
  exact Bool.false_ne_true this

end Ladner

/-! ### Ladner's theorem -/

/-- **Ladner's theorem.** In any abstract complexity world (see `CS.World`), if `P ≠ NP`
then there is an `NP`-intermediate language: a language which is in `NP`, is not in `P`,
and is not `NP`-complete. -/
