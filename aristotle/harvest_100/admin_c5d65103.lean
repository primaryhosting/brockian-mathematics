import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial
open scoped IntermediateField

namespace Math2

/-- A *Belyi map* (in the genus-zero, polynomial model): a nonconstant polynomial with
rational coefficients, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`.  Being a polynomial, such a map is totally
ramified over `∞`, so it is ramified only above `{0, 1, ∞}`. -/
def IsBelyiMap (f : ℚ[X]) : Prop :=
  0 < f.natDegree ∧ ∀ z : ℂ, aeval z (derivative f) = 0 → aeval z f ∈ ({0, 1} : Set ℂ)

/-- `BelyiFor S` says that there is a Belyi map sending every point of `S` into the
branch locus `{0, 1, ∞}` (concretely, into `{0,1}`). -/
def BelyiFor (S : Set ℂ) : Prop :=
  ∃ f : ℚ[X], IsBelyiMap f ∧ ∀ s ∈ S, aeval s f ∈ ({0, 1} : Set ℂ)

/-- The degree over `ℚ` of a complex number (junk value `0` for transcendentals). -/
noncomputable def adeg (z : ℂ) : ℕ := (minpoly ℚ z).natDegree

/-! ### Composition -/

/-- Composing a Belyi map for `T` with a map `g` whose critical values and whose values
on `S` all lie in `T` produces a Belyi map for `S`. -/
theorem belyi_comp (g : ℚ[X]) (hg : 0 < g.natDegree) (S T : Set ℂ)
    (hcrit : ∀ z : ℂ, aeval z (derivative g) = 0 → aeval z g ∈ T)
    (hS : ∀ s ∈ S, aeval s g ∈ T) (hT : BelyiFor T) : BelyiFor S := by
  obtain ⟨f, ⟨hfdeg, hfcrit⟩, hfT⟩ := hT
  refine ⟨f.comp g, ⟨?_, ?_⟩, ?_⟩
  · rw [natDegree_comp]; positivity
  · intro z hz
    rw [derivative_comp, map_mul, mul_eq_zero] at hz
    rw [aeval_comp]
    rcases hz with h | h
    · exact hfT _ (hcrit z h)
    · rw [aeval_comp] at h
      exact hfcrit _ h
  · intro s hs
    rw [aeval_comp]
    exact hfT _ (hS s hs)

theorem belyi_mono {S T : Set ℂ} (h : S ⊆ T) (hT : BelyiFor T) : BelyiFor S := by
  obtain ⟨f, hf, hfT⟩ := hT
  exact ⟨f, hf, fun s hs => hfT s (h hs)⟩

/-! ### The easy direction -/

theorem isAlgebraic_of_belyi {f : ℚ[X]} (hf : IsBelyiMap f) {s : ℂ}
    (hs : aeval s f ∈ ({0, 1} : Set ℂ)) : IsAlgebraic ℚ s := by
  obtain ⟨hdeg, -⟩ := hf
  rcases hs with h | h
  · exact ⟨f, fun hf0 => by simp [hf0] at hdeg, h⟩
  · refine ⟨f - 1, ?_, by simp [map_sub, Set.mem_singleton_iff.mp h]⟩
    intro h0
    have : f = 1 := by linear_combination (norm := ring_nf) h0
    simp [this] at hdeg

/-! ### Belyi's pushing construction -/

/-- Evaluating a rational polynomial at a rational point, viewed in `ℂ`. -/
theorem aeval_rat (p : ℚ[X]) (q : ℚ) : aeval ((q : ℂ)) p = ((p.eval q : ℚ) : ℂ) := by
  have h : ((q : ℂ)) = algebraMap ℚ ℂ q := by simp
  rw [h, aeval_algebraMap_apply]; simp

/-- The normalized Belyi polynomial `((m+n)^(m+n) / (m^m n^n)) * X^m * (1-X)^n`. -/
noncomputable def belyiPush (m n : ℕ) : ℚ[X] :=
  C (((m + n : ℚ) ^ (m + n)) / ((m : ℚ) ^ m * (n : ℚ) ^ n)) * (X ^ m * (1 - X) ^ n)

theorem belyiPush_eq (m n : ℕ) : belyiPush (m + 1) (n + 1) =
    C ((((m : ℚ) + 1 + ((n : ℚ) + 1)) ^ ((m + 1) + (n + 1))) /
        (((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1)))
      * ((X : ℚ[X]) ^ (m + 1) * (1 - X) ^ (n + 1)) := by
  unfold belyiPush; push_cast; ring_nf

/-- The derivative of `X^m (1-X)^n`, for `m, n ≥ 1`. -/
theorem derivative_pow_mul_one_sub_pow (m n : ℕ) :
    derivative ((X : ℚ[X]) ^ (m + 1) * (1 - X) ^ (n + 1)) =
      X ^ m * (1 - X) ^ n * (C ((m : ℚ) + 1) - C ((m : ℚ) + (n : ℚ) + 2) * X) := by
  simp only [derivative_mul, derivative_pow, derivative_X, derivative_sub, derivative_one,
    Polynomial.C_add, Polynomial.C_1, map_ofNat]
  push_cast
  simp only [Polynomial.C_add, Polynomial.C_1]
  ring

theorem belyiPush_eval_zero (m n : ℕ) : (belyiPush (m + 1) (n + 1)).eval 0 = 0 := by
  rw [belyiPush_eq]; simp

theorem belyiPush_eval_one (m n : ℕ) : (belyiPush (m + 1) (n + 1)).eval 1 = 0 := by
  rw [belyiPush_eq]; simp

/-- `belyiPush (m+1) (n+1)` sends `(m+1)/(m+n+2)` to `1`. -/
theorem belyiPush_eval_ratio (m n : ℕ) :
    (belyiPush (m + 1) (n + 1)).eval (((m : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2)) = 1 := by
  have ha : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hb : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hs : ((m : ℚ) + (n : ℚ) + 2) ≠ 0 := by positivity
  unfold belyiPush
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  push_cast
  have h1 : (1 : ℚ) - ((m : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2)
      = ((n : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2) := by field_simp; ring
  rw [h1, div_pow, div_pow, show ((m : ℚ) + 1 + ((n : ℚ) + 1)) = ((m : ℚ) + (n : ℚ) + 2) by ring,
    pow_add]
  field_simp

/-- Every critical value of `belyiPush (m+1) (n+1)` lies in `{0,1}`. -/
theorem belyiPush_crit (m n : ℕ) (z : ℂ)
    (hz : aeval z (derivative (belyiPush (m + 1) (n + 1))) = 0) :
    aeval z (belyiPush (m + 1) (n + 1)) ∈ ({0, 1} : Set ℂ) := by
  have hcC : ((((m : ℚ) + 1 + ((n : ℚ) + 1)) ^ ((m + 1) + (n + 1)) /
      (((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1)) : ℚ) : ℂ) ≠ 0 := by
    have hc : (((m : ℚ) + 1 + ((n : ℚ) + 1)) ^ ((m + 1) + (n + 1))) /
        (((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1)) ≠ 0 := by positivity
    exact_mod_cast hc
  rw [belyiPush_eq, derivative_C_mul, derivative_pow_mul_one_sub_pow] at hz
  simp only [map_mul, map_sub, aeval_C, aeval_X, map_pow, map_one] at hz
  have hz3 : z = ((0 : ℚ) : ℂ) ∨ z = ((1 : ℚ) : ℂ) ∨
      z = ((((m : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2) : ℚ) : ℂ) := by
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd (by simpa using h) hcC
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with hz0 | hz1
      · rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp at hz0
        · left
          have := (pow_eq_zero_iff (n := m) (a := z) hm.ne').mp hz0
          simpa using this
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp at hz1
        · right; left
          have h' := (pow_eq_zero_iff (n := n) (a := (1 - z)) hn.ne').mp hz1
          have : z = 1 := by linear_combination -h'
          simpa using this
    · right; right
      have hne : ((m : ℂ) + (n : ℂ) + 2) ≠ 0 := by
        have : ((m : ℚ) + (n : ℚ) + 2) ≠ 0 := by positivity
        exact_mod_cast this
      simp only [map_add, map_one, map_natCast, map_ofNat] at h2
      push_cast
      rw [eq_div_iff hne]
      linear_combination -h2
  rcases hz3 with h | h | h <;> rw [h, aeval_rat]
  · left; rw [belyiPush_eval_zero]; simp
  · left; rw [belyiPush_eval_one]; simp
  · right; rw [belyiPush_eval_ratio]; simp

theorem belyiPush_natDegree (m n : ℕ) : 0 < (belyiPush (m + 1) (n + 1)).natDegree := by
  have hc : (((m : ℚ) + 1 + ((n : ℚ) + 1)) ^ ((m + 1) + (n + 1))) /
      (((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1)) ≠ 0 := by positivity
  have hX : ((X : ℚ[X]) ^ (m + 1)) ≠ 0 := pow_ne_zero _ X_ne_zero
  have h1X : ((1 - X : ℚ[X]) ^ (n + 1)) ≠ 0 := by
    refine pow_ne_zero _ fun h => ?_
    have := congrArg (Polynomial.eval (0 : ℚ)) h
    simp at this
  unfold belyiPush
  rw [natDegree_C_mul (by push_cast; exact_mod_cast hc), natDegree_mul hX h1X]
  have h1 : (1 - X : ℚ[X]).natDegree = 1 := by compute_degree!
  simp [natDegree_pow, h1]

/-- Weighted AM–GM: `x^a (1-x)^b ≤ a^a b^b / (a+b)^(a+b)` on `[0,1]`. -/
theorem push_real_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (((a : ℝ) + (b : ℝ)) ^ (a + b) / ((a : ℝ) ^ a * (b : ℝ) ^ b)) * (x ^ a * (1 - x) ^ b) ≤ 1 := by
  have hA : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hB : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hM : (0 : ℝ) < (a : ℝ) + (b : ℝ) := by linarith
  have hx1 : (0 : ℝ) ≤ 1 - x := by linarith
  set w₁ : ℝ := (a : ℝ) / ((a : ℝ) + (b : ℝ)) with hw1
  set w₂ : ℝ := (b : ℝ) / ((a : ℝ) + (b : ℝ)) with hw2
  have hw1pos : 0 < w₁ := by rw [hw1]; positivity
  have hw2pos : 0 < w₂ := by rw [hw2]; positivity
  have hsum : w₁ + w₂ = 1 := by rw [hw1, hw2, ← add_div, div_self hM.ne']
  set p₁ : ℝ := x * ((a : ℝ) + (b : ℝ)) / (a : ℝ) with hp1
  set p₂ : ℝ := (1 - x) * ((a : ℝ) + (b : ℝ)) / (b : ℝ) with hp2
  have hp1nn : 0 ≤ p₁ := by rw [hp1]; positivity
  have hp2nn : 0 ≤ p₂ := by rw [hp2]; positivity
  have key := Real.geom_mean_le_arith_mean2_weighted hw1pos.le hw2pos.le hp1nn hp2nn hsum
  have harith : w₁ * p₁ + w₂ * p₂ = 1 := by rw [hw1, hw2, hp1, hp2]; field_simp; ring
  rw [harith] at key
  have hu : (0 : ℝ) ≤ p₁ ^ w₁ * p₂ ^ w₂ := by positivity
  have hpow : (p₁ ^ w₁ * p₂ ^ w₂) ^ ((a : ℝ) + (b : ℝ)) ≤ 1 := Real.rpow_le_one hu key hM.le
  have he1 : w₁ * ((a : ℝ) + (b : ℝ)) = (a : ℝ) := by rw [hw1]; field_simp
  have he2 : w₂ * ((a : ℝ) + (b : ℝ)) = (b : ℝ) := by rw [hw2]; field_simp
  have hrw : (p₁ ^ w₁ * p₂ ^ w₂) ^ ((a : ℝ) + (b : ℝ)) = p₁ ^ a * p₂ ^ b := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast p₁ a,
      ← Real.rpow_natCast p₂ b, ← Real.rpow_mul hp1nn, ← Real.rpow_mul hp2nn, he1, he2]
  rw [hrw] at hpow
  have hexp : p₁ ^ a * p₂ ^ b =
      (((a : ℝ) + (b : ℝ)) ^ (a + b) / ((a : ℝ) ^ a * (b : ℝ) ^ b)) * (x ^ a * (1 - x) ^ b) := by
    rw [hp1, hp2, div_pow, div_pow, mul_pow, mul_pow, pow_add]
    field_simp
  rw [hexp] at hpow
  exact hpow

/-- `belyiPush` maps `[0,1]` into `[0,1]` (weighted AM–GM). -/
theorem belyiPush_mem_Icc (m n : ℕ) {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ (belyiPush (m + 1) (n + 1)).eval t ∧ (belyiPush (m + 1) (n + 1)).eval t ≤ 1 := by
  have hev : (belyiPush (m + 1) (n + 1)).eval t =
      ((((m : ℚ) + 1 + ((n : ℚ) + 1)) ^ ((m + 1) + (n + 1))) /
        (((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1))) * (t ^ (m + 1) * (1 - t) ^ (n + 1)) := by
    rw [belyiPush_eq]; simp
  refine ⟨?_, ?_⟩
  · rw [hev]
    have : (0 : ℚ) ≤ 1 - t := by linarith
    positivity
  · rw [hev]
    have hreal := push_real_le (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) (t : ℝ)
      (by exact_mod_cast h0) (by exact_mod_cast h1)
    have hcast : ((((((m : ℚ) + 1 + ((n : ℚ) + 1)) ^ ((m + 1) + (n + 1))) /
        (((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1))) *
          (t ^ (m + 1) * (1 - t) ^ (n + 1)) : ℚ) : ℝ) ≤ 1 := by
      push_cast
      convert hreal using 3 <;> push_cast <;> ring
    exact_mod_cast hcast

/-! ### The rational case -/

/-- Any rational number in `(0,1)` is of the form `(m+1)/(m+n+2)`. -/
theorem exists_ratio (l : ℚ) (h0 : 0 < l) (h1 : l < 1) :
    ∃ m n : ℕ, l = ((m : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2) := by
  have hnum : 0 < l.num := Rat.num_pos.mpr h0
  have hdq : (0 : ℚ) < (l.den : ℚ) := by exact_mod_cast l.pos
  have hlt : l.num < (l.den : ℤ) := by
    rw [← Rat.num_div_den l, div_lt_one hdq] at h1
    exact_mod_cast h1
  set a : ℕ := l.num.toNat with ha
  have ha1 : 1 ≤ a := by omega
  have had : a + 1 ≤ l.den := by omega
  refine ⟨a - 1, l.den - a - 1, ?_⟩
  have e1 : (a - 1 : ℕ) + 1 = a := by omega
  have e2 : (a - 1 : ℕ) + (l.den - a - 1 : ℕ) + 2 = l.den := by omega
  have hm : ((a - 1 : ℕ) : ℚ) + 1 = (a : ℚ) := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℚ)) e1
  have hd : ((a - 1 : ℕ) : ℚ) + ((l.den - a - 1 : ℕ) : ℚ) + 2 = (l.den : ℚ) := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℚ)) e2
  rw [hm, hd]
  have hna : (a : ℚ) = (l.num : ℚ) := by
    rw [ha]; exact_mod_cast congrArg (fun x : ℤ => (x : ℚ)) (Int.toNat_of_nonneg hnum.le)
  rw [hna]
  exact (Rat.num_div_den l).symm

/-- The identity is a Belyi map for any set of points already lying in `{0,1}`. -/
theorem belyi_zero_one (S : Set ℂ) (h : ∀ s ∈ S, s ∈ ({0, 1} : Set ℂ)) : BelyiFor S := by
  refine ⟨X, ⟨by simp, ?_⟩, ?_⟩
  · intro z hz; simp at hz
  · intro s hs; simpa using h s hs

/-- Belyi's theorem for a finite set of rationals contained in `[0,1]`, by induction on the
number of points different from `0` and `1`. -/
theorem belyi_rat_Icc : ∀ (k : ℕ) (T : Finset ℚ), (∀ t ∈ T, 0 ≤ t ∧ t ≤ 1) →
    (T.filter (fun t => t ≠ 0 ∧ t ≠ 1)).card ≤ k →
    BelyiFor ((fun q : ℚ => (q : ℂ)) '' (T : Set ℚ)) := by
  intro k
  induction k with
  | zero =>
    intro T _ hcard
    refine belyi_zero_one _ ?_
    rintro s ⟨t, ht, rfl⟩
    have hnot : t ∉ T.filter (fun t => t ≠ 0 ∧ t ≠ 1) := by
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)]; simp
    simp only [Finset.mem_filter, not_and, not_not] at hnot
    have h01 : t = 0 ∨ t = 1 := by
      by_cases h : t = 0
      · exact Or.inl h
      · exact Or.inr (hnot ht h)
    rcases h01 with rfl | rfl <;> simp
  | succ k ih =>
    intro T hT hcard
    by_cases hempty : ∀ t ∈ T, t = 0 ∨ t = 1
    · refine belyi_zero_one _ ?_
      rintro s ⟨t, ht, rfl⟩
      rcases hempty t ht with rfl | rfl <;> simp
    · push_neg at hempty
      obtain ⟨l, hlT, hl0, hl1⟩ := hempty
      obtain ⟨hl0', hl1'⟩ := hT l hlT
      have hlpos : 0 < l := lt_of_le_of_ne hl0' (Ne.symm hl0)
      have hllt : l < 1 := lt_of_le_of_ne hl1' hl1
      obtain ⟨m, n, hmn⟩ := exists_ratio l hlpos hllt
      have hgl : (belyiPush (m + 1) (n + 1)).eval l = 1 := by
        rw [hmn]; exact belyiPush_eval_ratio m n
      set g := belyiPush (m + 1) (n + 1) with hg
      set T₁ : Finset ℚ := insert 0 (insert 1 (T.image (fun t => g.eval t))) with hT₁
      have hmem01 : ∀ t ∈ T₁, 0 ≤ t ∧ t ≤ 1 := by
        intro t ht
        simp only [hT₁, Finset.mem_insert, Finset.mem_image] at ht
        rcases ht with rfl | rfl | ⟨u, hu, rfl⟩
        · norm_num
        · norm_num
        · exact belyiPush_mem_Icc m n (hT u hu).1 (hT u hu).2
      have hlfilter : l ∈ T.filter (fun t => t ≠ 0 ∧ t ≠ 1) :=
        Finset.mem_filter.mpr ⟨hlT, hl0, hl1⟩
      have hcard₁ : (T₁.filter (fun t => t ≠ 0 ∧ t ≠ 1)).card ≤ k := by
        have hsub : T₁.filter (fun t => t ≠ 0 ∧ t ≠ 1) ⊆
            ((T.filter (fun t => t ≠ 0 ∧ t ≠ 1)).erase l).image (fun t => g.eval t) := by
          intro x hx
          rw [Finset.mem_filter] at hx
          obtain ⟨hxmem, hx0, hx1⟩ := hx
          simp only [hT₁, Finset.mem_insert, Finset.mem_image] at hxmem
          rcases hxmem with rfl | rfl | ⟨t, ht, rfl⟩
          · exact absurd rfl hx0
          · exact absurd rfl hx1
          · refine Finset.mem_image.mpr
              ⟨t, Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨ht, ?_, ?_⟩⟩, rfl⟩
            · rintro rfl; exact hx1 hgl
            · rintro rfl; exact hx0 (belyiPush_eval_zero m n)
            · rintro rfl; exact hx0 (belyiPush_eval_one m n)
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_image_le (s := (T.filter (fun t => t ≠ 0 ∧ t ≠ 1)).erase l)
          (f := fun t => g.eval t)
        have h3 : ((T.filter (fun t => t ≠ 0 ∧ t ≠ 1)).erase l).card
            = (T.filter (fun t => t ≠ 0 ∧ t ≠ 1)).card - 1 :=
          Finset.card_erase_of_mem hlfilter
        have h4 : 1 ≤ (T.filter (fun t => t ≠ 0 ∧ t ≠ 1)).card :=
          Finset.card_pos.mpr ⟨l, hlfilter⟩
        omega
      refine belyi_comp g (belyiPush_natDegree m n) _ _ ?_ ?_ (ih T₁ hmem01 hcard₁)
      · intro z hz
        rcases belyiPush_crit m n z hz with h | h
        · refine ⟨0, by simp [hT₁], ?_⟩
          have hgz : aeval z g = 0 := h
          simp [hgz]
        · refine ⟨1, by simp [hT₁], ?_⟩
          have hgz : aeval z g = 1 := h
          simp [hgz]
      · rintro s ⟨t, ht, rfl⟩
        refine ⟨g.eval t, ?_, ?_⟩
        · simp only [hT₁, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_image]
          exact Or.inr (Or.inr ⟨t, ht, rfl⟩)
        · rw [aeval_rat]

/-- Belyi's theorem for an arbitrary finite set of rational points. -/
theorem belyi_rat (T : Finset ℚ) : BelyiFor ((fun q : ℚ => (q : ℂ)) '' (T : Set ℚ)) := by
  classical
  set M : ℚ := ∑ t ∈ T, |t| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun t _ => abs_nonneg t
  have hden : (0 : ℚ) < 2 * M + 1 := by linarith
  set L : ℚ[X] := C (2 * M + 1)⁻¹ * (X + C M) with hL
  have hLeval : ∀ t : ℚ, L.eval t = (t + M) / (2 * M + 1) := by
    intro t; simp [hL, div_eq_inv_mul]
  have hLdeg : 0 < L.natDegree := by
    have hc : (2 * M + 1)⁻¹ ≠ 0 := by positivity
    rw [hL, natDegree_C_mul hc]
    have : ((X : ℚ[X]) + C M).natDegree = 1 := by compute_degree!
    omega
  set T' : Finset ℚ := T.image (fun t => L.eval t) with hT'
  have hT'mem : ∀ t ∈ T', 0 ≤ t ∧ t ≤ 1 := by
    intro t ht
    rw [hT', Finset.mem_image] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have habs : |u| ≤ M := Finset.single_le_sum (f := fun t => |t|) (fun i _ => abs_nonneg i) hu
    have h1 : -M ≤ u := neg_le_of_abs_le habs
    have h2 : u ≤ M := le_of_abs_le habs
    rw [hLeval]
    exact ⟨div_nonneg (by linarith) (by linarith), by rw [div_le_one hden]; linarith⟩
  refine belyi_comp L hLdeg _ _ ?_ ?_ (belyi_rat_Icc T'.card T' hT'mem (Finset.card_filter_le _ _))
  · intro z hz
    exfalso
    rw [hL] at hz
    simp only [derivative_mul, derivative_C, derivative_X, zero_mul, add_zero, zero_add,
      mul_one, map_add, aeval_C] at hz
    have hne : ((2 * M + 1)⁻¹ : ℚ) ≠ 0 := by positivity
    have hcast : (((2 * M + 1)⁻¹ : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hne
    exact hcast (by simpa using hz)
  · rintro s ⟨t, ht, rfl⟩
    exact ⟨L.eval t, by rw [hT']; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ht),
      (aeval_rat L t).symm ▸ rfl⟩

/-! ### Descent on the degree -/

theorem isIntegral_aeval {β : ℂ} (hβ : IsAlgebraic ℚ β) (p : ℚ[X]) :
    IsIntegral ℚ (aeval β p) := by
  have hi : IsIntegral ℚ β := hβ.isIntegral
  have hfd : FiniteDimensional ℚ ℚ⟮β⟯ := IntermediateField.adjoin.finiteDimensional hi
  have hmem : aeval β p ∈ ℚ⟮β⟯ :=
    (IntermediateField.algebra_adjoin_le_adjoin ℚ {β}) (aeval_mem_adjoin_singleton ℚ β)
  have := (IsIntegral.of_finite ℚ (⟨aeval β p, hmem⟩ : ℚ⟮β⟯)).map (ℚ⟮β⟯.val)
  simpa using this

theorem isAlgebraic_aeval {β : ℂ} (hβ : IsAlgebraic ℚ β) (p : ℚ[X]) :
    IsAlgebraic ℚ (aeval β p) := (isIntegral_aeval hβ p).isAlgebraic

theorem adeg_aeval_le {β : ℂ} (hβ : IsAlgebraic ℚ β) (p : ℚ[X]) :
    adeg (aeval β p) ≤ adeg β := by
  have hi : IsIntegral ℚ β := hβ.isIntegral
  have hfd : FiniteDimensional ℚ ℚ⟮β⟯ := IntermediateField.adjoin.finiteDimensional hi
  have hmem : aeval β p ∈ ℚ⟮β⟯ :=
    (IntermediateField.algebra_adjoin_le_adjoin ℚ {β}) (aeval_mem_adjoin_singleton ℚ β)
  have hle : ℚ⟮aeval β p⟯ ≤ ℚ⟮β⟯ := IntermediateField.adjoin_simple_le_iff.mpr hmem
  unfold adeg
  rw [← IntermediateField.adjoin.finrank hi,
    ← IntermediateField.adjoin.finrank (isIntegral_aeval hβ p)]
  exact IntermediateField.finrank_le_of_le_right hle

/-- Base case of the descent: points of degree at most one, i.e. rational points. -/
theorem belyi_deg_le_one (S : Finset ℂ) (halg : ∀ s ∈ S, IsAlgebraic ℚ s)
    (hdeg : ∀ s ∈ S, adeg s ≤ 1) : BelyiFor (S : Set ℂ) := by
  classical
  have key : ∀ s ∈ S, ∃ q : ℚ, (q : ℂ) = s := by
    intro s hs
    have hint : IsIntegral ℚ s := (halg s hs).isIntegral
    have hpos : 0 < (minpoly ℚ s).natDegree := minpoly.natDegree_pos hint
    have h1 : (minpoly ℚ s).natDegree = 1 := le_antisymm (hdeg s hs) hpos
    obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact ⟨q, by simpa using hq⟩
  choose! g hg using key
  refine belyi_mono ?_ (belyi_rat (S.image g))
  rintro s hs
  exact ⟨g s, by simpa using ⟨s, hs, rfl⟩, hg s hs⟩

/-- Inductive step of the descent, at fixed maximal degree `d + 1 ≥ 2`: applying the minimal
polynomial of a point of maximal degree strictly decreases the number of points of that degree,
while introducing only critical values of smaller degree. -/
theorem belyi_descent_step (d : ℕ)
    (ih : ∀ S : Finset ℂ, (∀ s ∈ S, IsAlgebraic ℚ s) → (∀ s ∈ S, adeg s ≤ d) →
      BelyiFor (S : Set ℂ)) (hd : 1 ≤ d) :
    ∀ (k : ℕ) (S : Finset ℂ), (∀ s ∈ S, IsAlgebraic ℚ s) → (∀ s ∈ S, adeg s ≤ d + 1) →
      (S.filter (fun s => adeg s = d + 1)).card ≤ k → BelyiFor (S : Set ℂ) := by
  classical
  intro k
  induction k with
  | zero =>
    intro S halg hdeg hcard
    refine ih S halg fun s hs => ?_
    have hnot : s ∉ S.filter (fun s => adeg s = d + 1) := by
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)]; simp
    simp only [Finset.mem_filter, not_and] at hnot
    have h1 := hnot hs
    have h2 := hdeg s hs
    omega
  | succ k ihk =>
    intro S halg hdeg hcard
    by_cases hall : ∀ s ∈ S, adeg s ≤ d
    · exact ih S halg hall
    · push_neg at hall
      obtain ⟨α, hαS, hα⟩ := hall
      have hαdeg : adeg α = d + 1 := le_antisymm (hdeg α hαS) hα
      have hαalg : IsAlgebraic ℚ α := halg α hαS
      have hαint : IsIntegral ℚ α := hαalg.isIntegral
      set m : ℚ[X] := minpoly ℚ α with hm
      have hmdeg : m.natDegree = d + 1 := hαdeg
      have hderivdeg : (derivative m).natDegree ≤ d := by
        have := Polynomial.natDegree_derivative_lt (p := m) (by omega)
        omega
      have hderiv0 : derivative m ≠ 0 := by
        intro h0
        have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero (R := ℚ) h0
        omega
      have hmα : aeval α m = 0 := minpoly.aeval ℚ α
      set C₁ : Finset ℂ := ((derivative m).aroots ℂ).toFinset with hC₁
      have hC₁mem : ∀ z : ℂ, aeval z (derivative m) = 0 → z ∈ C₁ := by
        intro z hz
        rw [hC₁, Multiset.mem_toFinset, Polynomial.mem_aroots]
        exact ⟨hderiv0, hz⟩
      have hC₁deg : ∀ z ∈ C₁, IsAlgebraic ℚ z ∧ adeg z ≤ d := by
        intro z hz
        rw [hC₁, Multiset.mem_toFinset, Polynomial.mem_aroots] at hz
        obtain ⟨-, hz2⟩ := hz
        refine ⟨⟨derivative m, hderiv0, hz2⟩, ?_⟩
        have hdle := minpoly.degree_le_of_ne_zero ℚ z hderiv0 hz2
        have h2 : adeg z ≤ (derivative m).natDegree := Polynomial.natDegree_le_natDegree hdle
        omega
      set S' : Finset ℂ := S.image (fun s => aeval s m) ∪ C₁.image (fun z => aeval z m) with hS'
      have hS'alg : ∀ x ∈ S', IsAlgebraic ℚ x := by
        intro x hx
        rw [hS', Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
        rcases hx with ⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩
        · exact isAlgebraic_aeval (halg s hs) m
        · exact isAlgebraic_aeval (hC₁deg z hz).1 m
      have hS'deg : ∀ x ∈ S', adeg x ≤ d + 1 := by
        intro x hx
        rw [hS', Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
        rcases hx with ⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩
        · exact le_trans (adeg_aeval_le (halg s hs) m) (hdeg s hs)
        · exact le_trans (le_trans (adeg_aeval_le (hC₁deg z hz).1 m) (hC₁deg z hz).2) (by omega)
      have hzero : adeg (0 : ℂ) = 1 := minpoly.natDegree_eq_one_iff.mpr ⟨0, by simp⟩
      have hαfilter : α ∈ S.filter (fun s => adeg s = d + 1) := Finset.mem_filter.mpr ⟨hαS, hαdeg⟩
      have hcard' : (S'.filter (fun s => adeg s = d + 1)).card ≤ k := by
        have hsub : S'.filter (fun s => adeg s = d + 1) ⊆
            ((S.filter (fun s => adeg s = d + 1)).erase α).image (fun s => aeval s m) := by
          intro x hx
          rw [Finset.mem_filter] at hx
          obtain ⟨hxmem, hxdeg⟩ := hx
          rw [hS', Finset.mem_union, Finset.mem_image, Finset.mem_image] at hxmem
          rcases hxmem with ⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩
          · refine Finset.mem_image.mpr
              ⟨s, Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hs, ?_⟩⟩, rfl⟩
            · rintro rfl
              rw [hmα] at hxdeg
              omega
            · have h1 := adeg_aeval_le (halg s hs) m
              have h2 := hdeg s hs
              omega
          · exfalso
            have h1 := adeg_aeval_le (hC₁deg z hz).1 m
            have h2 := (hC₁deg z hz).2
            omega
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_image_le (s := (S.filter (fun s => adeg s = d + 1)).erase α)
          (f := fun s => aeval s m)
        have h3 := Finset.card_erase_of_mem hαfilter
        have h4 : 1 ≤ (S.filter (fun s => adeg s = d + 1)).card := Finset.card_pos.mpr ⟨α, hαfilter⟩
        omega
      refine belyi_comp m (by omega) _ _ ?_ ?_ (ihk S' hS'alg hS'deg hcard')
      · intro z hz
        refine Finset.mem_coe.mpr ?_
        rw [hS', Finset.mem_union]
        exact Or.inr (Finset.mem_image_of_mem _ (hC₁mem z hz))
      · intro s hs
        refine Finset.mem_coe.mpr ?_
        rw [hS', Finset.mem_union]
        exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hs))

/-- Belyi's theorem for finite sets of algebraic numbers of bounded degree, by induction on the
degree bound. -/
theorem belyi_of_adeg_le : ∀ (d : ℕ) (S : Finset ℂ), (∀ s ∈ S, IsAlgebraic ℚ s) →
    (∀ s ∈ S, adeg s ≤ d) → BelyiFor (S : Set ℂ) := by
  intro d
  induction d with
  | zero =>
    intro S halg hdeg
    exact belyi_deg_le_one S halg fun s hs => le_trans (hdeg s hs) (by omega)
  | succ d ihd =>
    intro S halg hdeg
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact belyi_deg_le_one S halg hdeg
    · exact belyi_descent_step d ihd hd (S.filter (fun s => adeg s = d + 1)).card S halg hdeg
        le_rfl

/-- **Belyi's theorem** (the hard direction), in the genus-zero model: any finite set of
algebraic numbers can be sent into `{0, 1, ∞}` by a Belyi map. -/
theorem belyi_exists (S : Finset ℂ) (halg : ∀ s ∈ S, IsAlgebraic ℚ s) :
    BelyiFor (S : Set ℂ) := by
  classical
  exact belyi_of_adeg_le (S.sup adeg) S halg fun s hs => Finset.le_sup (f := adeg) hs

/-! ### The theorem -/

/-- **Belyi's theorem**, in the genus-zero (marked `ℙ¹`) model.

A finite set of points `S ⊆ ℙ¹(ℂ)` is defined over `ℚ̄` (that is, all its points are
algebraic numbers) if and only if there is a Belyi map, i.e. a nonconstant morphism
`f : ℙ¹ → ℙ¹` defined over `ℚ` which is ramified only above `{0, 1, ∞}` and which maps
the marked points `S` into `{0, 1, ∞}`.

Here `f` is realized as a polynomial `f ∈ ℚ[X]`: such a map is totally ramified over `∞`,
and the hypothesis in `IsBelyiMap` says that all of its finite critical values lie in
`{0, 1}`. -/
theorem belyi_theorem (S : Finset ℂ) :
    (∀ s ∈ S, IsAlgebraic ℚ s) ↔
      ∃ f : ℚ[X], IsBelyiMap f ∧ ∀ s ∈ S, aeval s f ∈ ({0, 1} : Set ℂ) := by
  constructor
  · intro h
    obtain ⟨f, hf, hfS⟩ := belyi_exists S h
    exact ⟨f, hf, fun s hs => hfS s hs⟩
  · rintro ⟨f, hf, hfS⟩ s hs
    exact isAlgebraic_of_belyi hf (hfS s hs)

/-- **Belyi's theorem** for a single marked point: a complex number is algebraic if and only if
some Belyi map sends it into the branch locus `{0, 1, ∞}`. -/
theorem belyi_theorem_point (s : ℂ) :
    IsAlgebraic ℚ s ↔
      ∃ f : ℚ[X], IsBelyiMap f ∧ aeval s f ∈ ({0, 1} : Set ℂ) := by
  classical
  constructor
  · intro h
    obtain ⟨f, hf, hfS⟩ := (belyi_theorem {s}).mp (by simpa using h)
    exact ⟨f, hf, hfS s (by simp)⟩
  · rintro ⟨f, hf, hfs⟩
    exact isAlgebraic_of_belyi hf hfs

end Math2

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

