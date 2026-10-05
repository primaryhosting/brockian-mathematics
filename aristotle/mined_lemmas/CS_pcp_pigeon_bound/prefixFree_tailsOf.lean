/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kraft's inequality for prefix-free binary codes

A finite set `S` of binary codewords (lists of booleans) is *prefix-free* if no codeword
is a prefix of a different codeword.  The main result, `CS.pcp_pigeon_bound`, states
Kraft's inequality: `∑ w ∈ S, (1/2) ^ w.length ≤ 1`.
-/

namespace CS

/-- A finite set of binary codewords is *prefix-free* when no codeword is a prefix of
another codeword. -/

lemma prefixFree_tailsOf {b : Bool} {S : Finset (List Bool)} (h0 : [] ∉ S)
    (hS : PrefixFree S) : PrefixFree (tailsOf b S) := by
  intro u hu v hv huv
  rw [mem_tailsOf h0] at hu hv
  have : (b :: u) <+: (b :: v) := by
    exact List.cons_prefix_cons.mpr ⟨rfl, huv⟩
  have := hS _ hu _ hv this
  exact List.cons_injective this

