import Mathlib

open scoped BigOperators
open scoped Classical

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Local constellation counts

For a *constellation* (admissible tuple) `H = (h₁, …, h_k)` of integer shifts, the
*local count* at a modulus `p` is the number of residue classes `a mod p` for which none of
`a + h₁, …, a + h_k` is divisible by `p`; equivalently, the number of `a : ZMod p` with
`a + hᵢ ≠ 0` for all `i`.

This file gives the general closed formula (`Brockian.localCount_eq`) and specializes it to
tuples of length one, two and three; the `k = 3` case is
`Brockian.ConstellationLocalCountK3`, with an arithmetic (divisibility) restatement in
`Brockian.ConstellationLocalCountK3_dvd`.
-/

namespace Brockian

/-- The local constellation count of the shift set `H` at modulus `p`: the number of residues
`a : ZMod p` such that `a + h ≠ 0` for every shift `h ∈ H`. -/

theorem localCount_eq (p : ℕ) [NeZero p] (H : Finset ℤ) :
    localCount p H = p - (H.image (fun h : ℤ => -(h : ZMod p))).card := by
  have key : (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + (h : ZMod p) ≠ 0))
      = (H.image (fun h : ℤ => -(h : ZMod p)))ᶜ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      Finset.mem_image, not_exists, not_and]
    exact ⟨fun h x hx hc => h x hx (by rw [← hc]; ring),
      fun h x hx hc => h x hx (by linear_combination -hc)⟩
  rw [localCount, key, Finset.card_compl, ZMod.card]

/-- The empty constellation: every residue is allowed. -/
