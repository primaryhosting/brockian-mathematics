import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open Polynomial

variable {α : Type*}

/-- The natural-number rank function of a matroid. -/
noncomputable def mrk (M : Matroid α) (S : Set α) : ℕ := (M.eRk S).toNat

/-- The characteristic polynomial of a matroid `M` on a finite ground set,
in Whitney rank generating form `χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`.
Here the ground set is the whole (finite) type, i.e. this is intended for `M.E = Set.univ`. -/
noncomputable def charPoly [Fintype α] (M : Matroid α) : Polynomial ℤ :=
  ∑ S : Finset α, (-1) ^ S.card * X ^ (mrk M Set.univ - mrk M (S : Set α))

/-- The `i`-th unsigned Whitney number of the first kind: the absolute value of the
coefficient of `X ^ i` in the characteristic polynomial. -/
noncomputable def whitney [Fintype α] (M : Matroid α) (i : ℕ) : ℕ :=
  ((charPoly M).coeff i).natAbs

/-- Log-concavity of a sequence of natural numbers. -/
def LogConcaveSeq (w : ℕ → ℕ) : Prop := ∀ i, w i * w (i + 2) ≤ w (i + 1) * w (i + 1)

/-! ### Binomial coefficients are log-concave -/

/-- The binomial coefficients `k ↦ C(n, k)` form a log-concave sequence. -/
theorem choose_log_concave (n i : ℕ) :
    n.choose i * n.choose (i + 2) ≤ n.choose (i + 1) * n.choose (i + 1) := by
  have h1 : n.choose (i + 1) * (i + 1) = n.choose i * (n - i) := Nat.choose_succ_right_eq n i
  have h2 : n.choose (i + 2) * (i + 2) = n.choose (i + 1) * (n - (i + 1)) :=
    Nat.choose_succ_right_eq n (i + 1)
  have key : (n.choose i * n.choose (i + 2)) * ((i + 1) * (i + 2))
      ≤ (n.choose (i + 1) * n.choose (i + 1)) * ((i + 1) * (i + 2)) := by
    have e1 : (n.choose i * n.choose (i + 2)) * ((i + 1) * (i + 2))
        = (n.choose i * n.choose (i + 1)) * ((n - (i + 1)) * (i + 1)) := by
      calc (n.choose i * n.choose (i + 2)) * ((i + 1) * (i + 2))
          = n.choose i * (n.choose (i + 2) * (i + 2)) * (i + 1) := by ring
        _ = n.choose i * (n.choose (i + 1) * (n - (i + 1))) * (i + 1) := by rw [h2]
        _ = (n.choose i * n.choose (i + 1)) * ((n - (i + 1)) * (i + 1)) := by ring
    have e2 : (n.choose (i + 1) * n.choose (i + 1)) * ((i + 1) * (i + 2))
        = (n.choose i * n.choose (i + 1)) * ((n - i) * (i + 2)) := by
      calc (n.choose (i + 1) * n.choose (i + 1)) * ((i + 1) * (i + 2))
          = n.choose (i + 1) * (n.choose (i + 1) * (i + 1)) * (i + 2) := by ring
        _ = n.choose (i + 1) * (n.choose i * (n - i)) * (i + 2) := by rw [h1]
        _ = (n.choose i * n.choose (i + 1)) * ((n - i) * (i + 2)) := by ring
    rw [e1, e2]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-! ### The rank function of the Boolean (free) matroid -/

theorem mrk_freeOn_univ (S : Set α) :
    mrk (Matroid.freeOn (Set.univ : Set α)) S = S.encard.toNat := by
  rw [mrk, Matroid.eRk_freeOn (Set.subset_univ S)]

theorem mrk_freeOn_coe_finset [Fintype α] (S : Finset α) :
    mrk (Matroid.freeOn (Set.univ : Set α)) (S : Set α) = S.card := by
  rw [mrk_freeOn_univ, Set.encard_coe_eq_coe_finsetCard]
  simp

theorem mrk_freeOn_ground [Fintype α] :
    mrk (Matroid.freeOn (Set.univ : Set α)) Set.univ = Fintype.card α := by
  rw [mrk_freeOn_univ, ← Finset.coe_univ, Set.encard_coe_eq_coe_finsetCard]
  simp

/-! ### The characteristic polynomial of the Boolean (free) matroid -/

theorem charPoly_freeOn [Fintype α] :
    charPoly (Matroid.freeOn (Set.univ : Set α)) =
      ∑ k ∈ Finset.range (Fintype.card α + 1),
        ((Fintype.card α).choose k : Polynomial ℤ) * (-1) ^ k * X ^ (Fintype.card α - k) := by
  have hgroup : ∀ f : ℕ → Polynomial ℤ, ∑ S : Finset α, f S.card
      = ∑ k ∈ Finset.range (Fintype.card α + 1), (Fintype.card α).choose k • f k := by
    intro f
    rw [← Finset.powerset_univ, Finset.sum_powerset]
    refine Finset.sum_congr (by simp [Finset.card_univ]) ?_
    intro k _
    rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_powersetCard.1 ht).2]),
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ]
  have hcp : charPoly (Matroid.freeOn (Set.univ : Set α))
      = ∑ S : Finset α, ((-1 : Polynomial ℤ)) ^ S.card * X ^ (Fintype.card α - S.card) := by
    refine Finset.sum_congr rfl ?_
    intro S _
    rw [mrk_freeOn_ground, mrk_freeOn_coe_finset]
  rw [hcp, hgroup (fun k => ((-1 : Polynomial ℤ)) ^ k * X ^ (Fintype.card α - k))]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [nsmul_eq_mul]
  ring

/-- The characteristic polynomial of the Boolean (free) matroid on an `n`-element
ground set is `(X - 1) ^ n`. -/
theorem charPoly_freeOn_eq_pow [Fintype α] :
    charPoly (Matroid.freeOn (Set.univ : Set α)) = (X - 1) ^ (Fintype.card α) := by
  set n := Fintype.card α with hn
  rw [charPoly_freeOn]
  have h : ((X : Polynomial ℤ) - 1) ^ n = (X + (-1)) ^ n := by ring
  rw [h, add_pow, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp only [Finset.mem_range] at hk
  have hk' : k ≤ n := by omega
  have h0 : n + 1 - 1 - k = n - k := by omega
  have h1 : n - (n - k) = k := by omega
  rw [h0, h1, Nat.choose_symm hk']
  ring

theorem coeff_charPoly_freeOn [Fintype α] (i : ℕ) :
    (charPoly (Matroid.freeOn (Set.univ : Set α))).coeff i
      = (-1) ^ (Fintype.card α - i) * ((Fintype.card α).choose i : ℤ) := by
  set n := Fintype.card α with hn
  rw [charPoly_freeOn, Polynomial.finset_sum_coeff]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (((n.choose k : Polynomial ℤ)) * (-1) ^ k * X ^ (n - k)).coeff i
        = if n - k = i then ((n.choose k : ℤ)) * (-1) ^ k else 0 := by
    intro k _
    have h : ((n.choose k : Polynomial ℤ)) * (-1) ^ k = C (((n.choose k : ℤ)) * (-1) ^ k) := by
      push_cast [Polynomial.C_mul, Polynomial.C_pow]
      simp
    rw [h, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp [eq_comm]
  rw [Finset.sum_congr rfl hterm]
  by_cases hi : i ≤ n
  · rw [Finset.sum_eq_single (n - i)]
    · rw [if_pos (by omega), Nat.choose_symm hi]
      ring
    · intro k hk hne
      rw [Finset.mem_range] at hk
      rw [if_neg (by omega)]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Finset.sum_eq_zero]
    · simp
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [if_neg (by omega)]

/-- The unsigned Whitney numbers of the Boolean (free) matroid on an `n`-element ground
set are the binomial coefficients `C(n, i)`. -/
theorem whitney_freeOn [Fintype α] (i : ℕ) :
    whitney (Matroid.freeOn (Set.univ : Set α)) i = (Fintype.card α).choose i := by
  rw [whitney, coeff_charPoly_freeOn, Int.natAbs_mul]
  simp [Int.natAbs_pow]

/-- **Log-concavity of the coefficients of the characteristic polynomial of a matroid**
(Adiprasito–Huh–Katz), proved here in the base case of the Boolean (free) matroid on a
finite ground set: the absolute values of the coefficients of the characteristic
polynomial form a log-concave sequence. -/
theorem huh_matroid_log_concave (α : Type*) [Fintype α] :
    LogConcaveSeq (whitney (Matroid.freeOn (Set.univ : Set α))) := by
  intro i
  simp only [whitney_freeOn]
  exact choose_log_concave _ i

end Frontier

