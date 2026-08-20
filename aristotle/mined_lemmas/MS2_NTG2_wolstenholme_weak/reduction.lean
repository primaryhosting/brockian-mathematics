import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma reduction {A B C : ℤ} (hA : 0 < A) (hD : 0 < 4 * A * C - B ^ 2) {x₀ y₀ : ℤ}
    (hne0 : ¬(x₀ = 0 ∧ y₀ = 0))
    (hmin : ∀ x y : ℤ, ¬(x = 0 ∧ y = 0) → qb A B C x₀ y₀ ≤ qb A B C x y) :
    ∃ x₁ y₁ : ℤ, x₀ * y₁ - x₁ * y₀ = 1 ∧
      (2 * A * x₀ * x₁ + B * (x₀ * y₁ + x₁ * y₀) + 2 * C * y₀ * y₁) ^ 2 ≤
        qb A B C x₀ y₀ ^ 2 ∧
      qb A B C x₀ y₀ ≤ qb A B C x₁ y₁ := by
  set m := qb A B C x₀ y₀ with hm
  have hmpos : 0 < m := qb_pos hA hD hne0
  -- the minimal vector is primitive
  have hgcd : Int.gcd x₀ y₀ = 1 := by
    have hg0 : Int.gcd x₀ y₀ ≠ 0 := by
      intro h
      have h' := Int.gcd_eq_zero_iff.mp h
      exact hne0 ⟨h'.1, h'.2⟩
    obtain ⟨u, hu⟩ : (Int.gcd x₀ y₀ : ℤ) ∣ x₀ := Int.gcd_dvd_left x₀ y₀
    obtain ⟨v, hv⟩ : (Int.gcd x₀ y₀ : ℤ) ∣ y₀ := Int.gcd_dvd_right x₀ y₀
    set g : ℤ := (Int.gcd x₀ y₀ : ℤ) with hgdef
    have hgpos : 0 < g := by
      rw [hgdef]; exact_mod_cast Nat.pos_of_ne_zero hg0
    have huv : ¬(u = 0 ∧ v = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hne0 ⟨by simp [hu], by simp [hv]⟩
    have hsm : m = g ^ 2 * qb A B C u v := by rw [hm, hu, hv, qb_smul]
    have h1 : m ≤ qb A B C u v := hmin u v huv
    have h2 : 1 ≤ g := hgpos
    have hqpos : 0 < qb A B C u v := lt_of_lt_of_le hmpos h1
    have hkey : (g ^ 2 - 1) * qb A B C u v ≤ 0 := by nlinarith [hsm, h1]
    have hg2 : g ^ 2 ≤ 1 := by nlinarith [hkey, hqpos]
    have hgle : g ≤ 1 := by nlinarith [hg2, h2]
    simp only [hgdef] at hgle h2
    omega
  -- complete to a basis
  obtain ⟨a, b, hab⟩ : IsCoprime x₀ y₀ := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  -- `a * x₀ + b * y₀ = 1`
  set x₁' : ℤ := -b with hx1
  set y₁' : ℤ := a with hy1
  have hdet : x₀ * y₁' - x₁' * y₀ = 1 := by rw [hx1, hy1]; linarith [hab]
  set B' : ℤ := 2 * A * x₀ * x₁' + B * (x₀ * y₁' + x₁' * y₀) + 2 * C * y₀ * y₁' with hB'
  -- shift to make the middle coefficient small
  set k : ℤ := -((B' + m) / (2 * m)) with hk
  have hdet2 : x₀ * (y₁' + k * y₀) - (x₁' + k * x₀) * y₀ = 1 := by rw [← hdet]; ring
  refine ⟨x₁' + k * x₀, y₁' + k * y₀, hdet2, ?_, ?_⟩
  · have hexp : 2 * A * x₀ * (x₁' + k * x₀) +
        B * (x₀ * (y₁' + k * y₀) + (x₁' + k * x₀) * y₀) + 2 * C * y₀ * (y₁' + k * y₀)
        = B' + 2 * k * m := by
      rw [hB', hm]; unfold qb; ring
    rw [hexp]
    have h2m : 0 < 2 * m := by omega
    have hr1 : 0 ≤ (B' + m) % (2 * m) := Int.emod_nonneg _ (by omega)
    have hr2 : (B' + m) % (2 * m) < 2 * m := Int.emod_lt_of_pos _ h2m
    have hdiv : (B' + m) % (2 * m) = (B' + m) - (2 * m) * ((B' + m) / (2 * m)) :=
      Int.emod_def _ _
    have : B' + 2 * k * m = (B' + m) % (2 * m) - m := by rw [hk]; linarith [hdiv]
    rw [this]
    nlinarith [hr1, hr2]
  · refine hmin _ _ ?_
    rintro ⟨h1, h2⟩
    rw [h1, h2] at hdet2
    simp at hdet2

/-- **Lagrange's bound**: a positive definite integral binary quadratic form takes a value `m`
on a nonzero vector with `3 m² ≤ 4AC - B²`. -/
