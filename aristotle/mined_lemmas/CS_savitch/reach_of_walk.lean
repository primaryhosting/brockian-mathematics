/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Savitch.Model
import RequestProject.Savitch.Interp

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
`NSPACE f ⊆ DSPACE (16 * (f + 1)^2)`, i.e. Savitch's theorem, and the corollary
`PSPACE = NPSPACE`.

The model of computation is set up in `RequestProject.Savitch.Model`: a device is
a configuration graph with read-only access to the input tape, and the space it
uses is the number of bits needed to encode a configuration.

The proof follows the classical argument.  Given a nondeterministic device `M`
using `s` bits of space, its configuration graph (extended by a single absorbing
accepting vertex) has at most `2 ^ (s+1)` vertices, so acceptance amounts to
reachability in a graph of that size.  Reachability is computed deterministically
by the midpoint recursion `reach` of `RequestProject.Savitch.Reach`, of depth
`K = s + 1`, and this recursion is executed by the explicit stack machine of
`RequestProject.Savitch.Interp`, whose states consist of at most `K` frames, each
holding three vertices and a bit.  That machine therefore has at most
`2 ^ (16 * K ^ 2)` configurations, i.e. it runs in space `O(s²)`.
-/

namespace CS

/-! ### Counting the states of the evaluator -/

section Card

variable {C : Type} [Fintype C] (K : ℕ)

/-- Encoding of a state of the evaluator by its mode and the (padded) list of its
frames. -/

lemma reach_of_walk : ∀ (k : ℕ) {v : ℕ → C} {ℓ : ℕ} {a b : C},
    Walk R v ℓ a b → ℓ ≤ 2 ^ k → reach R k a b = true := by
  intro k
  induction k with
  | zero =>
      rintro v ℓ a b ⟨h0, hl, hstep⟩ hle
      simp only [pow_zero] at hle
      interval_cases ℓ
      · exact bdec_of (Or.inl (by rw [← h0, ← hl]))
      · have := hstep 0 (by norm_num)
        rw [h0] at this
        rw [show (0 : ℕ) + 1 = 1 from rfl] at this
        exact bdec_of (Or.inr (by rw [← hl]; exact this))
  | succ k ih =>
      rintro v ℓ a b ⟨h0, hl, hstep⟩ hle
      set i := min ℓ (2 ^ k) with hi
      have hile : i ≤ ℓ := min_le_left _ _
      have hi1 : i ≤ 2 ^ k := min_le_right _ _
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      have hi2 : ℓ - i ≤ 2 ^ k := by omega
      have w1 : Walk R v i a (v i) := ⟨h0, rfl, fun j hj => hstep j (lt_of_lt_of_le hj hile)⟩
      have w2 : Walk R (fun t => v (i + t)) (ℓ - i) (v i) b :=
        ⟨by simp, by simp only []; rw [Nat.add_sub_cancel' hile]; exact hl,
         fun j hj => by
           have : i + j < ℓ := by omega
           simpa [Nat.add_assoc] using hstep (i + j) this⟩
      simp only [reach_succ, bdec_eq_true_iff]
      exact ⟨v i, ih w1 hi1, ih w2 hi2⟩

