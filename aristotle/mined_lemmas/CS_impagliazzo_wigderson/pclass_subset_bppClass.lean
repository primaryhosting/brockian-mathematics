/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses only the Lean 4 core library),
so that the file can literally begin with the header comment above.

Encoding conventions:
* an input of length `n` is a natural number `x` (thought of as the bit string
  `x.testBit 0, …, x.testBit (n-1)`);
* a random string of length `r` is a natural number `ρ < 2 ^ r`;
* probabilities are handled by counting: `count r f` is the number of strings of length `r`
  on which `f` returns `true`, and a probability statement `p ≥ 2/3` is written as
  `2 * 2 ^ r ≤ 3 * count r f`.
-/

namespace CS

/-! ## Counting -/

/-- The number of strings `ρ < 2 ^ r` on which `f` returns `true`. -/

theorem pclass_subset_bppClass (M : Model) (L : Lang) (hL : M.PClass L) : M.BPPClass L := by
  refine ⟨fun _ => 0, ⟨0, fun n => by simp⟩, fun n x _ => L n x, M.ignore_rand hL, ?_⟩
  intro n x
  have h : (fun _ : Nat => (L n x == L n x)) = (fun _ : Nat => true) := by
    funext ρ; simp
  rw [h, count_const_true]
  omega

/-- **Impagliazzo–Wigderson.**  In any model of computation for which the
hardness-versus-randomness tradeoff holds (strong circuit lower bounds yield a pseudorandom
generator with logarithmic seed length, fooling polynomial-time tests, whose seeds can be
enumerated in polynomial time), strong circuit lower bounds — the existence of a language in
`E` requiring circuits of size `2 ^ Ω(n)` — imply `P = BPP`. -/
