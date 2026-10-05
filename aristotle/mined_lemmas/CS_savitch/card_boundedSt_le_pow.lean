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

lemma card_boundedSt_le_pow (hcard : Fintype.card C ≤ 2 ^ K) (hK : 1 ≤ K) :
    Fintype.card { p : St C // p.2.length ≤ K } ≤ 2 ^ (16 * K ^ 2) := by
  set N := Fintype.card C with hN
  have h1 : N * N + 2 ≤ 2 ^ (2 * K + 1) := by
    have hNN : N * N ≤ 2 ^ K * 2 ^ K := Nat.mul_le_mul hcard hcard
    have : (2 : ℕ) ^ K * 2 ^ K = 2 ^ (2 * K) := by ring
    have h2K : (2 : ℕ) ^ 1 ≤ 2 ^ (2 * K) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ (2 * K + 1) = 2 ^ (2 * K) + 2 ^ (2 * K) := by ring
    omega
  have h2 : N ^ 3 * 2 + 1 ≤ 2 ^ (3 * K + 2) := by
    have hN3 : N ^ 3 ≤ (2 ^ K) ^ 3 := Nat.pow_le_pow_left hcard 3
    have he : ((2 : ℕ) ^ K) ^ 3 = 2 ^ (3 * K) := by rw [← pow_mul]; ring_nf
    have h1K : (1 : ℕ) ≤ 2 ^ (3 * K) := Nat.one_le_two_pow
    have : (2 : ℕ) ^ (3 * K + 2) = 2 ^ (3 * K) * 4 := by ring
    omega
  have h3 : (N ^ 3 * 2 + 1) ^ K ≤ (2 ^ (3 * K + 2)) ^ K := Nat.pow_le_pow_left h2 K
  have h4 : Fintype.card { p : St C // p.2.length ≤ K } ≤ 2 ^ (2 * K + 1) * (2 ^ (3 * K + 2)) ^ K :=
    (card_boundedSt_le K).trans (Nat.mul_le_mul h1 h3)
  refine h4.trans ?_
  rw [← pow_mul, ← pow_add]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  nlinarith [sq_nonneg K, hK]

end Card

/-! ### Adding a unique accepting configuration -/

section Lift

variable {Γ : Type} (M : NDevice Γ)

/-- Input head position, on the configuration space extended by a sink. -/
