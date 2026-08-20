/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math2

/-- The dimensions in which the Kervaire invariant is known (or, in the single remaining
edge case, permitted) to be nonzero: `2, 6, 14, 30, 62, 126`. -/
def IsKervaireDimension (n : Nat) : Prop :=
  n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126

/-- **Browder's constraint, arithmetic form.**  A positive natural number `n` with `n + 2` a
power of two and `n ≤ 126` is one of `2, 6, 14, 30, 62, 126`. -/
theorem isKervaireDimension_of_add_two_eq_pow
    {n j : Nat} (hn : n + 2 = 2 ^ j) (hpos : 0 < n) (hle : n ≤ 126) :
    IsKervaireDimension n := by
  unfold IsKervaireDimension
  have hj : j ≤ 7 := by
    match Nat.lt_or_ge j 8 with
    | Or.inl h => omega
    | Or.inr h =>
        have h1 : (2 : Nat) ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) h
        have h2 : (2 : Nat) ^ 8 = 256 := rfl
        omega
  match j, hj with
  | 0, _ =>
      have e : (2 : Nat) ^ 0 = 1 := rfl
      omega
  | 1, _ =>
      have e : (2 : Nat) ^ 1 = 2 := rfl
      omega
  | 2, _ =>
      have e : (2 : Nat) ^ 2 = 4 := rfl
      omega
  | 3, _ =>
      have e : (2 : Nat) ^ 3 = 8 := rfl
      omega
  | 4, _ =>
      have e : (2 : Nat) ^ 4 = 16 := rfl
      omega
  | 5, _ =>
      have e : (2 : Nat) ^ 5 = 32 := rfl
      omega
  | 6, _ =>
      have e : (2 : Nat) ^ 6 = 64 := rfl
      omega
  | 7, _ =>
      have e : (2 : Nat) ^ 7 = 128 := rfl
      omega
  | (k + 8), h => exact absurd h (by omega)

/-- **The Kervaire invariant one problem (Hill–Hopkins–Ravenel), dimension statement.**

Let `KervaireInvariantOne n` be any predicate on natural numbers expressing that there is a
closed framed manifold of dimension `n` with Kervaire invariant one (equivalently, a class of
Kervaire invariant one in the `n`-th stable stem).

Two classical inputs are taken as hypotheses:

* `browder`: Browder's theorem — such a dimension is positive and satisfies `n + 2 = 2 ^ j`
  for some `j`, i.e. `n = 2 ^ j - 2`;
* `hhr`: the Hill–Hopkins–Ravenel theorem — no such dimension exceeds `126`, i.e. the Kervaire
  invariant vanishes in the dimensions `2 ^ j - 2` for `j ≥ 8`.

Conclusion: the Kervaire invariant can be nonzero only in the dimensions
`2, 6, 14, 30, 62, 126`. -/
theorem kervaire_invariant
    (KervaireInvariantOne : Nat → Prop)
    (browder : ∀ n, KervaireInvariantOne n → 0 < n ∧ ∃ j : Nat, n + 2 = 2 ^ j)
    (hhr : ∀ n, KervaireInvariantOne n → n ≤ 126) :
    ∀ n, KervaireInvariantOne n → IsKervaireDimension n := by
  intro n hn
  match browder n hn with
  | ⟨hpos, ⟨j, hj⟩⟩ => exact isKervaireDimension_of_add_two_eq_pow hj hpos (hhr n hn)

end Math2

namespace Math2

/-- Non-vacuity check: the hypotheses of `Math2.kervaire_invariant` are satisfiable, e.g. by the
predicate that is true exactly on the six Kervaire dimensions. -/
theorem kervaire_hypotheses_satisfiable :
    (∀ n, IsKervaireDimension n → 0 < n ∧ ∃ j : Nat, n + 2 = 2 ^ j) ∧
      (∀ n, IsKervaireDimension n → n ≤ 126) := by
  constructor
  · intro n hn
    unfold IsKervaireDimension at hn
    match hn with
    | Or.inl h => exact ⟨by omega, 2, by omega⟩
    | Or.inr (Or.inl h) => exact ⟨by omega, 3, by omega⟩
    | Or.inr (Or.inr (Or.inl h)) => exact ⟨by omega, 4, by omega⟩
    | Or.inr (Or.inr (Or.inr (Or.inl h))) => exact ⟨by omega, 5, by omega⟩
    | Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))) => exact ⟨by omega, 6, by omega⟩
    | Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))) => exact ⟨by omega, 7, by omega⟩
  · intro n hn
    unfold IsKervaireDimension at hn
    omega

end Math2

#print axioms Math2.kervaire_invariant
#print axioms Math2.kervaire_hypotheses_satisfiable

