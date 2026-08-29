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

lemma PolyBounded.savitch {f : ℕ → ℕ} (hf : PolyBounded f) :
    PolyBounded (fun n => 16 * (f n + 1) ^ 2) := by
  obtain ⟨c, k, hc⟩ := hf
  refine ⟨16 * (c + 1) ^ 2, 2 * k, fun n => ?_⟩
  have h2 : (1 : ℕ) ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have h1 : f n + 1 ≤ (c + 1) * (n + 1) ^ k :=
    calc f n + 1 ≤ c * (n + 1) ^ k + 1 := Nat.add_le_add_right (hc n) 1
      _ ≤ c * (n + 1) ^ k + (n + 1) ^ k := Nat.add_le_add_left h2 _
      _ = (c + 1) * (n + 1) ^ k := by ring
  calc 16 * (f n + 1) ^ 2 ≤ 16 * ((c + 1) * (n + 1) ^ k) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)
    _ = 16 * (c + 1) ^ 2 * (n + 1) ^ (2 * k) := by
        rw [mul_pow, ← pow_mul]
        ring

/-- **`PSPACE = NPSPACE`**, an immediate corollary of Savitch's theorem. -/
