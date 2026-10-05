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

def world : World where
  inP := EC
  inNP := EC
  polyFun := polyFun
  M := enum
  sim := sim
  R := R
  simR := simR
  K := Kmodel
  P_subset_NP := fun _ h => h
  P_congr := by
    rintro L L' hLL' ⟨N, b, hb⟩
    exact ⟨N, b, fun x hx => by rw [← hLL' x]; exact hb x hx⟩
  P_empty := ⟨0, false, fun _ _ => rfl⟩
  P_finvar := by
    rintro L L' N hagree ⟨N1, b, hb⟩
    refine ⟨max N N1, b, fun x hx => ?_⟩
    rw [← hagree x (le_trans (le_max_left _ _) hx)]
    exact hb x (le_trans (le_max_right _ _) hx)
  P_red := by
    rintro A B r ⟨i, hr⟩ hAB hB
    obtain ⟨N', b', hE⟩ := enum_mem i
    refine ⟨N', if b' then B 1 else B 0, fun x hx => ?_⟩
    rw [hAB x, hr x, hE x hx]
    cases b' <;> simp
  NP_inter_P := by
    rintro A B ⟨N1, b1, h1⟩ ⟨N2, b2, h2⟩
    refine ⟨max N1 N2, b1 && b2, fun x hx => ?_⟩
    show (A x && B x) = (b1 && b2)
    rw [h1 x (le_trans (le_max_left _ _) hx), h2 x (le_trans (le_max_right _ _) hx)]
  M_mem := enum_mem
  M_surj := fun _ h => enum_surj h
  sim_mono := by rintro i x t t' b - hb; exact hb
  sim_sound := by rintro i x t b hb; simpa [sim, eq_comm] using hb
  sim_halts := fun i x => ⟨0, rfl⟩
  R_poly := fun j => ⟨j, fun _ => rfl⟩
  R_surj := fun r ⟨i, hi⟩ => ⟨i, fun x => (hi x).symm⟩
  simR_mono := by rintro j x t t' y - hy; exact hy
  simR_sound := by rintro j x t y hy; simpa [simR, eq_comm] using hy
  simR_halts := fun j x => ⟨0, rfl⟩
  K_NP := ⟨2, false, fun x hx => by simp [Kmodel]; omega⟩
  K_hard := by
    rintro A hA
    obtain ⟨i, hi⟩ := enum_surj hA
    refine ⟨R i, ⟨i, fun _ => rfl⟩, fun x => ?_⟩
    rw [← hi x]
    cases hb : enum i x <;> simp [R, hb, Kmodel]
  hole_inP := by
    obtain ⟨B, hB⟩ := hole_bounded
    obtain ⟨N, hN⟩ := eventually_const (hole_mono Kmodel sim simR) hB
    refine ⟨2 ^ N, decide (Even (hole Kmodel sim simR N)), fun x hx => ?_⟩
    show decide (Even (hole Kmodel sim simR (Nat.size x))) = _
    rw [hN _ (le_size_of_pow_le hx)]

end Model

/-- The axioms collected in `CS.World` are consistent: there is at least one world. -/
