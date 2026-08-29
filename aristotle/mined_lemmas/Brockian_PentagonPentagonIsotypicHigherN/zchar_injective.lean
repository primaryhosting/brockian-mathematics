/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian

open DihedralGroup

noncomputable section

/-! ## The root of unity -/

/-- A primitive `n`-th root of unity in `ℂ`. -/

lemma zchar_injective (n : ℕ) [NeZero n] : Function.Injective (zchar n) := by
  rcases eq_or_ne n 1 with rfl | hn
  · intro a b _; exact Subsingleton.elim a b
  · have hn2 : 1 < n := by have := Nat.pos_of_ne_zero (NeZero.ne n); omega
    intro a b hab
    have h1 : (1 : ZMod n).val = 1 := ZMod.val_one_eq_one_mod n ▸ Nat.mod_eq_of_lt hn2
    have h2 := congrArg (fun ψ => ψ (1 : ZMod n)) hab
    simp only [zchar_apply, h1, mul_one] at h2
    exact ZMod.val_injective n (((zta_prim n).pow_inj (ZMod.val_lt a) (ZMod.val_lt b)) h2)

/-! ## The isotypic vectors -/

/-- The `k`-th isotypic vector in the vertex space of the `n`-gon. -/
