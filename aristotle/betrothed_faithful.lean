/-!
# Betrothed Arithmetic Dynamics — repo-faithful, self-contained

Independent rebuild of the delivered `BetrothedDynamics.lean`, corrected to the
ACTUAL repo definitions in `Brockian/BetrothedNumbers.lean`:
  aliquot n = ∑ d ∈ n.properDivisors, d
  Betrothed m n := m ≠ n ∧ aliquot m = n + 1 ∧ aliquot n = m + 1
(The delivered file referenced `IsBetrothedPair`, which is defined nowhere in the
repo, so it could not compile. `partner n = σ n - n - 1 = aliquot n - 1`.)
Self-contained over Mathlib so a kernel (AXLE) can check it standalone.
-/
import Mathlib

open ArithmeticFunction

namespace Brockian.BetrothedNumbers.DynamicsFaithful

/-- Aliquot sum (repo-faithful): sum of proper divisors. -/
def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- Repo-faithful betrothed predicate. -/
def Betrothed (m n : ℕ) : Prop := m ≠ n ∧ aliquot m = n + 1 ∧ aliquot n = m + 1

/-- Partner map `n ↦ s(n) - 1` (equivalently `σ(n) - n - 1`). -/
def partner (n : ℕ) : ℕ := aliquot n - 1

theorem partner_eq_right {m n : ℕ} (h : Betrothed m n) : partner m = n := by
  obtain ⟨_, hm, _⟩ := h
  unfold partner
  omega

theorem partner_eq_left {m n : ℕ} (h : Betrothed m n) : partner n = m := by
  obtain ⟨_, _, hn⟩ := h
  unfold partner
  omega

/-- Betrothed pairs are exactly the nontrivial two-cycles of `partner`
(with each aliquot sum positive — which betrothed forces). -/
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

/-! ## Exact balance law in the `2^k p` construction family -/

/-- The forced odd partner in the `2^k p` construction. -/
def thabitPartner (k p : ℕ) : ℕ := (2 ^ k - 1) * (p + 2)

/-- Exact balance law under the delivered σ-criterion. The sign of
`p + 3 - 2^(k+1)` fixes the abundance class of the forced partner. -/
theorem thabit_balance_identity {k p : ℕ} (hk : 1 ≤ k)
    (hcriterion : ArithmeticFunction.sigma 1 (thabitPartner k p) = (2 ^ (k + 1) - 1) * (p + 1)) :
    ArithmeticFunction.sigma 1 (thabitPartner k p) + 2 ^ (k + 1) = 2 * thabitPartner k p + (p + 3) := by
  rw [hcriterion]
  unfold thabitPartner
  have hkpow : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  have hskpow : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  zify [hkpow, hskpow]
  ring

theorem thabit_deficient_iff {k p : ℕ} (hk : 1 ≤ k)
    (hcriterion : ArithmeticFunction.sigma 1 (thabitPartner k p) = (2 ^ (k + 1) - 1) * (p + 1)) :
    ArithmeticFunction.sigma 1 (thabitPartner k p) < 2 * thabitPartner k p ↔ p + 3 < 2 ^ (k + 1) := by
  have hbalance := thabit_balance_identity hk hcriterion
  omega

theorem thabit_perfect_iff {k p : ℕ} (hk : 1 ≤ k)
    (hcriterion : ArithmeticFunction.sigma 1 (thabitPartner k p) = (2 ^ (k + 1) - 1) * (p + 1)) :
    ArithmeticFunction.sigma 1 (thabitPartner k p) = 2 * thabitPartner k p ↔ p + 3 = 2 ^ (k + 1) := by
  have hbalance := thabit_balance_identity hk hcriterion
  omega

theorem thabit_abundant_iff {k p : ℕ} (hk : 1 ≤ k)
    (hcriterion : ArithmeticFunction.sigma 1 (thabitPartner k p) = (2 ^ (k + 1) - 1) * (p + 1)) :
    2 * thabitPartner k p < ArithmeticFunction.sigma 1 (thabitPartner k p) ↔ 2 ^ (k + 1) < p + 3 := by
  have hbalance := thabit_balance_identity hk hcriterion
  omega

end Brockian.BetrothedNumbers.DynamicsFaithful
