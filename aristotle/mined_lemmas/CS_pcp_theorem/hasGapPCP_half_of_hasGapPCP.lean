-- Lean requires `import` to be the first command in a file; the required header
-- comment follows immediately below.
import Mathlib

/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

/-!
## Overview

We formalise the PCP theorem `NP = PCP(log n, 1)` in its standard *constraint-satisfaction*
(gap-CSP) form, in the non-uniform (advice) setting.

* A **constraint** reads a constant number of bits of a Boolean assignment and applies an
  arbitrary Boolean predicate to them.
* A language `L ⊆ {0,1}*` is in `InNP` if for every input length `n` there is a
  constraint system `Ψ` with polynomially many constraints, each of arity at most a constant
  `q`, over variables `0, 1, …` (the first `n` variables carry the input `x`, the remaining
  ones are the witness/proof variables), such that `x ∈ L` iff `Ψ` has a satisfying assignment
  extending `x`.  By the Tseitin transformation this is exactly non-uniform `NP` (`NP/poly`).
* A language is in `InPCP` (i.e. in `PCP(log n, 1)`) if the same holds with a *gap*: for
  `x ∉ L` **every** assignment extending `x` satisfies at most half of the constraints.
  Reading a uniformly random constraint of the system is precisely a verifier that uses
  `O(log n)` random bits (there are polynomially many constraints) and reads `O(1)` bits of the
  input/proof, with completeness `1` and soundness error `1/2`.

The inclusion `PCP(log n, 1) ⊆ NP` is proved unconditionally (`CS.inNP_of_hasGapPCP`), as is the
*gap amplification by repetition* step `CS.hasGapPCP_half_of_hasGapPCP`, which turns any constant
gap into the gap `1/2` while keeping the arity constant and the size polynomial.

The remaining, genuinely hard, content of the PCP theorem is isolated as
`CS.GapCSPHardness`: every language in `NP` admits a constant-gap constraint system.  This is
the combinatorial core proved by Arora–Safra and Arora–Lund–Motwani–Sudan–Szegedy (and by
Dinur's gap amplification); it is *not* proved here.  `CS.pcp_theorem` derives the class
equality `NP = PCP(log n, 1)` from it, and `CS.pcp_theorem_iff` shows unconditionally that the
two statements are equivalent.
-/

namespace CS

/-- An assignment of Boolean values to the variables `0, 1, 2, …`. -/
abbrev Assignment := ℕ → Bool

/-- A local constraint: a list of queried variables together with a Boolean predicate on the
answers.  Its *arity* is the number of queried variables. -/
structure Constraint where
  /-- The variables read by the constraint. -/
  vars : List ℕ
  /-- The predicate applied to the values read. -/
  pred : List Bool → Bool

/-- Whether a constraint is satisfied by an assignment. -/

theorem hasGapPCP_half_of_hasGapPCP {L : Set (List Bool)} {s : ℚ} (hs : s < 1)
    (h : HasGapPCP L s) : InPCP L := by
  -- We may assume `0 ≤ s`.
  have h' : HasGapPCP L (max s 0) := hasGapPCP_mono (le_max_left _ _) h
  have hs' : max s 0 < 1 := max_lt hs (by norm_num)
  set t : ℚ := max s 0 with ht
  clear_value t
  clear h hs ht
  -- choose the number of repetitions
  obtain ⟨k, hk⟩ : ∃ k : ℕ, t ^ k < 1 / 2 := exists_pow_lt_of_lt_one (by norm_num) hs'
  obtain ⟨q, c, k₀, hfam⟩ := h'
  refine ⟨k * q, c ^ k, k₀ * k, fun n => ?_⟩
  obtain ⟨Ψ, hne, hlen, har, hmain⟩ := hfam n
  refine ⟨iterCSP Ψ k, iterCSP_ne_nil hne k, ?_, arityLE_iterCSP har k, fun x hx => ?_⟩
  · rw [length_iterCSP]
    calc Ψ.length ^ k ≤ (c * (n + 1) ^ k₀) ^ k := Nat.pow_le_pow_left hlen k
      _ = c ^ k * (n + 1) ^ (k₀ * k) := by rw [mul_pow, ← pow_mul]
  · obtain ⟨hcomp, hsound⟩ := hmain x hx
    refine ⟨fun hxL => ?_, fun hxL a hax => ?_⟩
    · obtain ⟨a, hax, hsat⟩ := hcomp hxL
      exact ⟨a, hax, sat_iterCSP hsat k⟩
    · rw [satFrac_iterCSP]
      calc satFrac Ψ a ^ k ≤ t ^ k := pow_le_pow_left₀ (satFrac_nonneg Ψ a) (hsound hxL a hax) k
        _ ≤ 1 / 2 := le_of_lt hk

/-!
### The PCP theorem
-/

/-- **The PCP theorem**, `NP = PCP(log n, 1)`, in its gap-CSP formulation, derived from the
hard combinatorial core `GapCSPHardness` (constant-gap constraint systems for `NP`, the
