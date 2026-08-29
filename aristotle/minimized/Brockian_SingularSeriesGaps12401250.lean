/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- Primality of a natural number, stated in the usual way: `p ≥ 2` and every divisor of `p`
is `1` or `p`. (Spelled out here so that this file is fully self-contained.) -/

def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

def IsAdmissibleGapSet (H : List Nat) : Prop :=
  ∀ p : Nat, IsPrimeNat p → ∃ r, r < p ∧ ∀ h ∈ H, h % p ≠ r

/-- For every even gap `g`, the two-element pattern `{0, g}` is admissible. -/

theorem admissible_pair_of_even {g : Nat} (he : g % 2 = 0) : IsAdmissibleGapSet [0, g] := by
  intro p hp
  have hp2 : 2 ≤ p := hp.1
  by_cases hpe : p = 2
  · -- modulo `2` both `0` and `g` are `0`, so the class `1` is omitted
    subst hpe
    refine ⟨1, by omega, ?_⟩
    intro h hmem
    have hcases : h = 0 ∨ h = g := by simpa using hmem
    cases hcases with
    | inl h1 => subst h1; omega
    | inr h1 => subst h1; omega
  · -- for `p ≥ 3` two residues cannot cover all `p` classes
    have hp3 : 3 ≤ p := by omega
    refine ⟨if g % p = 1 then 2 else 1, by split <;> omega, ?_⟩
    intro h hmem
    have hcases : h = 0 ∨ h = g := by simpa using hmem
    have hmod : g % p < p := Nat.mod_lt _ (by omega)
    cases hcases with
    | inl h1 => subst h1; simp only [Nat.zero_mod]; split <;> omega
    | inr h1 => subst h1; split <;> omega

/-- **Singular Series Gaps 1240–1250.**  Every even gap `g` in the range `1240 ≤ g ≤ 1250`
gives an admissible pattern `{0, g}`; equivalently, the associated singular series is nonzero,
so no congruence obstruction rules out infinitely many prime pairs with that gap. -/

theorem SingularSeriesGaps12401250 :
    ∀ g : Nat, 1240 ≤ g → g ≤ 1250 → g % 2 = 0 → IsAdmissibleGapSet [0, g] :=
  fun _ _ _ he => admissible_pair_of_even he

/-- Sharpness of the parity condition: an odd gap is never admissible, since `0` and `g` then
cover both residue classes modulo `2`. -/
