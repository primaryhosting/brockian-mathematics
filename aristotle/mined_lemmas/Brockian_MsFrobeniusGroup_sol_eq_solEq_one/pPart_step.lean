import Mathlib

/-!
# Frobenius's theorem

For a finite group `G` and any `n`, `gcd (n, |G|)` divides the number of solutions of `xⁿ = 1`.

The proof is organised as follows.

* `sol G n` is the number of solutions of `x ^ n = 1`, `solEq n y` the number of solutions of
  `x ^ n = y`.
* `solEq_prime_pow_dvd`: if `y` has order `p ^ k` with `k ≥ 1`, then `p ^ a` divides the number
  of solutions of `x ^ (p ^ a) = y`.  (Each solution generates a cyclic group of order `p ^ (a+k)`
  containing `y`, and each such cyclic subgroup contains exactly `p ^ a` solutions.)
* Consequently `sol G (p ^ (a+1)) ≡ sol G (p ^ a) [MOD p ^ a]`, so all the numbers
  `sol G (p ^ b)` for `b ≥ a` are congruent mod `p ^ a`.
* `sol_mul_eq_sum`: writing `n = p ^ α * u` with `p ∤ u`, decomposing an element into its
  `p`-part and `p'`-part gives `sol G n = ∑_{w ^ u = 1} sol (centralizer w) (p ^ α)`.
* `pPart_dvd_sol_pPart` (the key theorem): the number of `p`-elements of `G` is divisible by the
  order of a Sylow `p`-subgroup.  This follows by induction on `|G|` from the previous identity
  applied to `n = |G|`, grouping the sum into conjugacy classes.
* Everything is then assembled.
-/

namespace Brockian.MsFrobeniusGroup

open scoped Classical
open Finset

universe u

variable {G : Type u} [Group G]

/-- The number of solutions of `x ^ n = 1` in `G`. -/

lemma pPart_step [Fintype G] {p : ℕ} (hp : p.Prime)
    (IH : ∀ (H : Type u) [Group H] [Fintype H], Nat.card H < Nat.card G →
      p ^ ((Nat.card H).factorization p) ∣ sol H (p ^ ((Nat.card H).factorization p))) :
    p ^ ((Nat.card G).factorization p) ∣ sol G (p ^ ((Nat.card G).factorization p)) := by
  -- Write |G| = p^v * m where p ∤ m
  set v := (Nat.card G).factorization p with hv_def
  obtain ⟨m, hm⟩ : ∃ m, Nat.card G = p ^ v * m ∧ ¬ p ∣ m := by
    use Nat.card G / p ^ v
    have hne : Nat.card G ≠ 0 := Nat.card_pos.ne'
    constructor
    · rw [Nat.mul_div_cancel' (Nat.ordProj_dvd _ _)]
    · intro hdvd
      have h1 : p ^ v ∣ Nat.card G := Nat.ordProj_dvd _ _
      have : p ^ (v + 1) ∣ Nat.card G := by
        rw [pow_succ]
        convert Nat.mul_dvd_mul_left (p ^ v) hdvd using 1
        exact (Nat.mul_div_cancel' h1).symm
      have hcontra : ¬ p ^ ((Nat.card G).factorization p + 1) ∣ Nat.card G :=
        Nat.pow_succ_factorization_not_dvd hne hp
      exact hcontra this
  have hv_pos : 0 < p ^ v := pow_pos hp.pos _
  have hm_pos : 0 < m := by nlinarith [Nat.card_pos (α := G)]
  -- sol G |G| = |G|
  have hcard : sol G (Nat.card G) = Nat.card G := sol_card_eq
  -- sol G (p^v * m) = ∑_{w^m=1} sol(centralizer w, p^v)
  have hdec := @sol_mul_eq_sum G _ _ p v m hp hm.2
  -- Split sum into central and non-central
  have hcard_eq : Nat.card G = p ^ v * m := hm.1
  -- sol G (p^v * m) = |G| = p^v * m
  have hsol_eq : sol G (p ^ v * m) = p ^ v * m := by
    calc sol G (p ^ v * m) = sol G (Nat.card G) := by rw [hcard_eq]
      _ = Nat.card G := hcard
      _ = p ^ v * m := hcard_eq
  -- Split the filter into central and non-central
  have hsplit : (univ.filter (fun w : G => w ^ m = 1)).sum
      (fun w => sol ↥(Subgroup.centralizer {w}) (p ^ v)) =
      (univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G)).sum
      (fun w => sol ↥(Subgroup.centralizer {w}) (p ^ v)) +
      (univ.filter (fun w : G => w ^ m = 1 ∧ w ∉ Subgroup.center G)).sum
      (fun w => sol ↥(Subgroup.centralizer {w}) (p ^ v)) := by
    rw [← Finset.sum_union]
    · congr 1
      ext w
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · exact Finset.disjoint_filter.mpr (fun x _ h1 h2 => h2.2 h1.2)
  -- Non-central sum is divisible by p^v by IH
  have hnoncen : p ^ v ∣ ∑ w ∈ univ.filter (fun w : G => w ^ m = 1 ∧ w ∉ Subgroup.center G),
      sol ↥(Subgroup.centralizer {w}) (p ^ v) := pPart_dvd_noncentral_sum hp IH m
  -- Central sum equals |center solutions| * sol G (p^v)
  have hcent : ∑ w ∈ univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G),
      sol ↥(Subgroup.centralizer {w}) (p ^ v) = sol ↥(Subgroup.center G) m * sol G (p ^ v) :=
    sum_central_eq m (p ^ v)
  -- So sol G (p^v * m) = c * sol G (p^v) + (multiple of p^v)
  have hmain : p ^ v * m = sol ↥(Subgroup.center G) m * sol G (p ^ v) +
      (univ.filter (fun w : G => w ^ m = 1 ∧ w ∉ Subgroup.center G)).sum
      (fun w => sol ↥(Subgroup.centralizer {w}) (p ^ v)) := by
    rw [← hsol_eq, hdec, hsplit, hcent]
  -- p^v divides the RHS sum, so p^v | sol(center G, m) * sol G (p^v)
  have hdiv : p ^ v ∣ sol ↥(Subgroup.center G) m * sol G (p ^ v) := by
    have : p ^ v ∣ p ^ v * m := dvd_mul_right _ _
    rw [hmain] at this
    exact Nat.dvd_add_left hnoncen |>.mp this
  -- sol(center G, m) is coprime to p (since center G is abelian and p ∤ m)
  have hcenter_not_dvd : ¬ p ∣ sol ↥(Subgroup.center G) m :=
    not_dvd_sol_of_comm (fun x y => Subtype.ext (Subgroup.mem_center_iff.mp x.2 y.1).symm) hp hm.2
  -- Therefore p^v and sol(center G, m) are coprime
  have hcoprime : Nat.Coprime (p ^ v) (sol ↥(Subgroup.center G) m) := by
    rcases Nat.eq_zero_or_pos v with hv_zero | hv_pos'
    · simp [hv_zero]
    · rw [Nat.coprime_pow_left_iff hv_pos']
      exact Nat.Prime.coprime_iff_not_dvd hp |>.mpr hcenter_not_dvd
  -- Conclude p^v | sol G (p^v)
  exact hcoprime.dvd_of_dvd_mul_left hdiv

/-- **Theorem P.**  The number of `p`-elements of a finite group is divisible by the order of a
Sylow `p`-subgroup.  Proof by induction on `|G|`: writing `|G| = p ^ v * m` with `p ∤ m`, the
primary decomposition identity gives `|G| = ∑_{w ^ m = 1} sol (centralizer w) (p ^ v)`.  The terms
with `w` non-central are divisible by `p ^ v` (by induction, after grouping into conjugacy
classes), and the central terms contribute `c * sol G (p ^ v)` where `c`, the number of central
`p'`-elements, is prime to `p`. -/
