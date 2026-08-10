import Mathlib
import Brockian.BetrothedNumbers

/-!
# Betrothed Arithmetic Dynamics

Reframes betrothed (quasi-amicable) pairs as nontrivial two-cycles of the
partner map `n ↦ s(n) - 1` (where `s = aliquot`, so `partner n = σ(n) - n - 1`),
and records the exact abundance **balance law** in the `2^k · p` construction
family: the sign of `(p + 3) - 2^(k+1)` fixes whether the forced partner is
deficient, perfect, or abundant.

Built on the repository predicate `Brockian.BetrothedNumbers.Betrothed`
(`m ≠ n ∧ aliquot m = n + 1 ∧ aliquot n = m + 1`). The two-cycle viewpoint is
classical (Hagis–Lord, *Quasi-Amicable Numbers*, 1977); the exact Lean statements
here are new to this repository. The balance law is **conditional** on the stated
σ-criterion for the construction (an explicit hypothesis, not an unproven axiom).

Kernel-checked against Lean 4.32.0 + Mathlib. Provenance: reconstructed and
corrected from a candidate `BetrothedDynamics.lean` that referenced an
`IsBetrothedPair` predicate absent from this repository.
-/

namespace Brockian.BetrothedNumbers.Dynamics

open Brockian.BetrothedNumbers

/-- The betrothed-partner map `n ↦ s(n) - 1`. A betrothed pair is a nontrivial
two-cycle of this map. -/
def partner (n : ℕ) : ℕ := aliquot n - 1

theorem partner_eq_right {m n : ℕ} (h : Betrothed m n) : partner m = n := by
  obtain ⟨_, hm, _⟩ := h
  unfold partner
  omega

theorem partner_eq_left {m n : ℕ} (h : Betrothed m n) : partner n = m := by
  obtain ⟨_, _, hn⟩ := h
  unfold partner
  omega

/-- Betrothed pairs are exactly the nontrivial two-cycles of `partner`, with each
aliquot sum positive (which betrothed forces, since `aliquot m = n + 1 ≥ 1`). -/
theorem betrothed_iff_twoCycle {m n : ℕ} :
    Betrothed m n ↔
      m ≠ n ∧ 1 ≤ aliquot m ∧ 1 ≤ aliquot n ∧ partner m = n ∧ partner n = m := by
  unfold partner
  constructor
  · rintro ⟨hne, hm, hn⟩
    refine ⟨hne, ?_, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨hne, hpm, hpn, hm, hn⟩
    exact ⟨hne, by omega, by omega⟩

theorem partner_involutive_on_pair {m n : ℕ} (h : Betrothed m n) :
    partner (partner m) = m := by
  rw [partner_eq_right h, partner_eq_left h]

theorem partner_ne_self_on_pair {m n : ℕ} (h : Betrothed m n) : partner m ≠ m := by
  rw [partner_eq_right h]
  exact h.1.symm

/-! ## Exact balance law in the `2^k · p` construction family -/

/-- The forced odd partner in the `2^k · p` construction, `(2^k - 1)(p + 2)`. -/
def thabitPartner (k p : ℕ) : ℕ := (2 ^ k - 1) * (p + 2)

/-- Exact balance law under the delivered σ-criterion. The sign of
`(p + 3) - 2^(k+1)` fixes the abundance class of the forced partner. The
subtraction-free form keeps the statement clean over `ℕ`. -/
theorem thabit_balance_identity {k p : ℕ} (hk : 1 ≤ k)
    (hcriterion :
      ArithmeticFunction.sigma 1 (thabitPartner k p) = (2 ^ (k + 1) - 1) * (p + 1)) :
    ArithmeticFunction.sigma 1 (thabitPartner k p) + 2 ^ (k + 1) =
      2 * thabitPartner k p + (p + 3) := by
  rw [hcriterion]
  unfold thabitPartner
  have hkpow : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  have hskpow : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  zify [hkpow, hskpow]
  ring

theorem thabit_deficient_iff {k p : ℕ} (hk : 1 ≤ k)
    (hcriterion :
      ArithmeticFunction.sigma 1 (thabitPartner k p) = (2 ^ (k + 1) - 1) * (p + 1)) :
    ArithmeticFunction.sigma 1 (thabitPartner k p) < 2 * thabitPartner k p ↔
      p + 3 < 2 ^ (k + 1) := by
  have hbalance := thabit_balance_identity hk hcriterion
  omega

theorem thabit_perfect_iff {k p : ℕ} (hk : 1 ≤ k)
    (hcriterion :
      ArithmeticFunction.sigma 1 (thabitPartner k p) = (2 ^ (k + 1) - 1) * (p + 1)) :
    ArithmeticFunction.sigma 1 (thabitPartner k p) = 2 * thabitPartner k p ↔
      p + 3 = 2 ^ (k + 1) := by
  have hbalance := thabit_balance_identity hk hcriterion
  omega

theorem thabit_abundant_iff {k p : ℕ} (hk : 1 ≤ k)
    (hcriterion :
      ArithmeticFunction.sigma 1 (thabitPartner k p) = (2 ^ (k + 1) - 1) * (p + 1)) :
    2 * thabitPartner k p < ArithmeticFunction.sigma 1 (thabitPartner k p) ↔
      2 ^ (k + 1) < p + 3 := by
  have hbalance := thabit_balance_identity hk hcriterion
  omega

end Brockian.BetrothedNumbers.Dynamics
