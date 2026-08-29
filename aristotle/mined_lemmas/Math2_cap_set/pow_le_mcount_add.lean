import Mathlib
/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
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

set_option grind.warning false

/-!
## The cap set problem

We prove the Croot–Lev–Pach / Ellenberg–Gijswijt bound: a subset of `𝔽₃ⁿ` containing no
non-trivial three-term arithmetic progression has size `o(3ⁿ)`.
-/

namespace CapSet

open Finset

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Points of `𝔽₃ⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → ZMod 3

/-- Exponent vectors of reduced monomials (each exponent is `0`, `1` or `2`). -/
abbrev Exp (n : ℕ) := Fin n → Fin 3

/-- The monomial function `x ↦ ∏ i, x i ^ α i` on `𝔽₃ⁿ`. -/

lemma pow_le_mcount_add {n d e : ℕ} (h : d + e + 1 = 2 * n) :
    3 ^ n ≤ mcount n d + mcount n e := by
  have hsub : (Finset.univ : Finset (Exp n)) ⊆
      Dset n d ∪ (Dset n e).image (fun α i => 2 - α i) := by
    intro α _
    rcases le_or_gt (edeg α) d with hd | hd
    · exact Finset.mem_union_left _ (mem_Dset.2 hd)
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨fun i => 2 - α i, mem_Dset.2 ?_, ?_⟩)
      · have := edeg_rev α; omega
      · funext i
        have h2 : ∀ a : Fin 3, 2 - (2 - a) = a := by decide
        exact h2 (α i)
  calc (3 : ℕ) ^ n = (Finset.univ : Finset (Exp n)).card := by simp
    _ ≤ (Dset n d ∪ (Dset n e).image (fun α i => 2 - α i)).card := Finset.card_le_card hsub
    _ ≤ (Dset n d).card + ((Dset n e).image (fun α i => 2 - α i)).card :=
        Finset.card_union_le _ _
    _ ≤ mcount n d + mcount n e := Nat.add_le_add_left Finset.card_image_le _
/-! ### The main combinatorial bound -/

