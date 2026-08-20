import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set `H` of integers is *admissible* if for every prime `p` it fails to cover
all residue classes modulo `p`, i.e. some residue class mod `p` is missed by `H`.
This is the classical admissibility condition of the Hardy–Littlewood prime `k`-tuple
conjecture. -/

lemma exists_residue_ne_pair {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a b : ZMod p) :
    ∃ r : ZMod p, a ≠ r ∧ b ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hcard : ({a, b} : Finset (ZMod p)).card < Fintype.card (ZMod p) := by
    have h1 : ({a, b} : Finset (ZMod p)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    have h2 : Fintype.card (ZMod p) = p := ZMod.card p
    omega
  have hne : ({a, b} : Finset (ZMod p))ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl]
    omega
  obtain ⟨r, hr⟩ := hne
  refine ⟨r, ?_, ?_⟩ <;> · rintro rfl; simp at hr

/-- An even natural number casts to `0` in `ZMod 2`. -/
