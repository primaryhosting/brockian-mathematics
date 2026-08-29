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

theorem derandomize_of_prg (M : Model) (r : Nat → Nat) (A : RAlg) (hA : M.RPoly r A)
    (L : Lang) (herr : ∀ n x, 2 * 2 ^ (r n) ≤ 3 * count (r n) (fun ρ => A n x ρ == L n x))
    (g : PRG M r) : M.Poly L := by
  have hB := g.derandomizes hA
  have key : ∀ n x,
      decide (2 ^ g.seedLen n < 2 * count (g.seedLen n) (fun y => A n x (g.gen n y)))
        = L n x := by
    intro n x
    have hR : 0 < 2 ^ (r n) := Nat.two_pow_pos _
    have hS : 0 < 2 ^ g.seedLen n := Nat.two_pow_pos _
    have hle := g.fools_le hA n x
    have hge := g.fools_ge hA n x
    have hcorr := herr n x
    cases hL : L n x with
    | false =>
        have hrewrite : (fun ρ => A n x ρ == L n x) = (fun ρ => !A n x ρ) := by
          funext ρ; simp [hL]
        rw [hrewrite] at hcorr
        have hsum := count_add_count_not (r n) (fun ρ => A n x ρ)
        have hrej : 3 * count (r n) (fun ρ => A n x ρ) ≤ 2 ^ (r n) := by omega
        have := minority_of_reject (R := 2 ^ (r n)) (S := 2 ^ g.seedLen n) hR hrej hge
        simp [Nat.not_lt.mpr this]
    | true =>
        have hrewrite : (fun ρ => A n x ρ == L n x) = (fun ρ => A n x ρ) := by
          funext ρ; simp [hL]
        rw [hrewrite] at hcorr
        have := majority_of_accept (R := 2 ^ (r n)) (S := 2 ^ g.seedLen n) hR hS hcorr hle
        simp [this]
  have hEq : (fun n x =>
      decide (2 ^ g.seedLen n < 2 * count (g.seedLen n) (fun y => A n x (g.gen n y)))) = L := by
    funext n x; exact key n x
  rwa [hEq] at hB

/-- `P ⊆ BPP` in any model. -/
