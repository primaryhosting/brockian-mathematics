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

open scoped BigOperators
open scoped Classical

namespace QI

/-- The `n`-bit state space, an `n`-dimensional vector space over `ZMod 2`. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟪y, x⟫ = ∑ i, y i * x i`. -/

theorem simon_recovery {n : ℕ} (s : Vec n) (hs : s ≠ 0) :
    ∃ Y : Fin n → Vec n, (∀ i, ip (Y i) s = 0) ∧
      ∀ t : Vec n, t ≠ 0 → (∀ i, ip (Y i) t = 0) → t = s := by
  obtain ⟨k, hk⟩ : ∃ k, s k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hs (funext hcon)
  have hk1 : s k = 1 := by revert hk; generalize s k = a; revert a; decide
  refine ⟨fun i => (fun j => (if j = i then 1 else 0) + s i * (if j = k then 1 else 0)), ?_, ?_⟩
  · intro i
    rw [ip_Y, hk1, mul_one]
    exact (by decide : ∀ a : ZMod 2, a + a = 0) (s i)
  · intro t ht h
    have h' : ∀ i, t i = s i * t k := by
      intro i
      have hi := h i
      rw [ip_Y] at hi
      have := congrArg (fun z => z + s i * t k) hi
      simpa [add_assoc, (by decide : ∀ a : ZMod 2, a + a = 0)] using this
    have htk : t k = 1 := by
      by_contra hc
      refine ht (funext fun i => ?_)
      have h0 : t k = 0 := by revert hc; generalize t k = a; revert a; decide
      simp [h' i, h0]
    funext i
    simp [h' i, htk]

/-! ## Classical side: `Ω(2 ^ (n / 2))` queries are necessary -/

/-- A canonical two-to-one map with period `s`: it picks, out of `{x, x + s}`, the element
that comes first in some fixed enumeration of `Vec n`. -/
