import RequestProject.Basic

/-!
# Unbounded fan-in Boolean circuits, the class `AC⁰`, and `PARITY`

A `Circuit n` is a Boolean circuit on `n` inputs built from constants, input
variables, negations, and *unbounded fan-in* `AND`/`OR` gates.

* `Circuit.depth` counts the maximal number of `AND`/`OR` gates on a root-to-leaf
  path (negations are free, as is standard for `AC⁰`).
* `Circuit.size` counts the number of `AND`/`OR` gates.

`InAC0 f` says that the family `f` is computed by circuits of some fixed depth and
polynomial size.  Making negations free and not counting them in the size only
makes the class larger, hence the lower bound proved later stronger.
-/

namespace CS

/-- Boolean circuits with unbounded fan-in `AND`/`OR` gates. -/
inductive Circuit (n : ℕ) where
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | neg : Circuit n → Circuit n
  | or : (m : ℕ) → (Fin m → Circuit n) → Circuit n
  | and : (m : ℕ) → (Fin m → Circuit n) → Circuit n

namespace Circuit

/-- The Boolean function computed by a circuit. -/

lemma exists_or_approx {n m ℓ E : ℕ} (q : Fin m → Fn n)
    (hq : ∀ i, q i ∈ Deg n E) (hq01 : ∀ i x, q i x = 0 ∨ q i x = 1) :
    ∃ F : Fn n, F ∈ Deg n (2 * ℓ * E) ∧ (∀ x, F x = 0 ∨ F x = 1) ∧
      ((Finset.univ : Finset (Bits n)).filter
        (fun x => F x ≠ bit (decide (∃ i, q i x = 1)))).card * 3 ^ ℓ ≤ 2 ^ n := by
  classical
  set Sf : (Fin ℓ → Fin m → ZMod 3) → Fin ℓ → Fn n := fun c j => ∑ i, c j i • q i with hSf
  set Gad : (Fin ℓ → Fin m → ZMod 3) → Fn n :=
    fun c => 1 - ∏ j : Fin ℓ, (1 - Sf c j * Sf c j) with hGad
  have hSval : ∀ c j x, Sf c j x = ∑ i, c j i * q i x := by
    intro c j x
    simp only [hSf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hGval : ∀ c x, Gad c x = 1 - ∏ j : Fin ℓ, (1 - Sf c j x * Sf c j x) := by
    intro c x
    simp only [hGad, Pi.sub_apply, Pi.one_apply, Finset.prod_apply, Pi.mul_apply]
  -- the degree bound
  have hdeg : ∀ c, Gad c ∈ Deg n (2 * ℓ * E) := by
    intro c
    have hS : ∀ j, Sf c j ∈ Deg n E := fun j =>
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hq i))
    have hfac : ∀ j : Fin ℓ, (1 - Sf c j * Sf c j) ∈ Deg n (E + E) := fun j =>
      Submodule.sub_mem _ one_mem_Deg (Deg_mul (hS j) (hS j))
    have hprod : (∏ j : Fin ℓ, (1 - Sf c j * Sf c j)) ∈ Deg n (∑ _j : Fin ℓ, (E + E)) :=
      Deg_prod _ _ _ (fun j _ => hfac j)
    have hsum : (∑ _j : Fin ℓ, (E + E)) = 2 * ℓ * E := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    rw [hsum] at hprod
    exact Submodule.sub_mem _ one_mem_Deg hprod
  -- the approximators are `0/1`-valued
  have hval01 : ∀ c x, Gad c x = 0 ∨ Gad c x = 1 := by
    intro c x
    rw [hGval]
    by_cases hz : ∃ j : Fin ℓ, (1 - Sf c j x * Sf c j x) = 0
    · obtain ⟨j, hj⟩ := hz
      right
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj]
      ring
    · push_neg at hz
      left
      have hone : ∀ j : Fin ℓ, (1 - Sf c j x * Sf c j x) = 1 := by
        intro j
        rcases ZMod3.sq_cases (Sf c j x) with h | h
        · rw [h]; ring
        · exact absurd (by rw [h]; ring) (hz j)
      rw [Finset.prod_congr rfl (fun j _ => hone j)]
      simp
  -- they are always correct when the `OR` is false
  have hzero : ∀ c x, (∀ i, q i x = 0) → Gad c x = 0 := by
    intro c x h0
    rw [hGval]
    have hone : ∀ j : Fin ℓ, (1 - Sf c j x * Sf c j x) = 1 := by
      intro j
      have hs : Sf c j x = 0 := by
        rw [hSval]
        exact Finset.sum_eq_zero (fun i _ => by rw [h0 i]; ring)
      rw [hs]; ring
    rw [Finset.prod_congr rfl (fun j _ => hone j)]
    simp
  -- an error forces all the random linear forms to vanish
  have hne : ∀ c x, Gad c x ≠ 1 → ∀ j, Sf c j x = 0 := by
    intro c x hcx j
    have hprodne : (∏ j : Fin ℓ, (1 - Sf c j x * Sf c j x)) ≠ 0 := by
      intro h0
      apply hcx
      rw [hGval, h0]; ring
    have hfacne : (1 - Sf c j x * Sf c j x) ≠ 0 := fun h0 =>
      hprodne (Finset.prod_eq_zero (Finset.mem_univ j) h0)
    rcases ZMod3.sq_cases (Sf c j x) with h | h
    · exact ZMod3.eq_zero_of_sq_eq_zero h
    · exact absurd (by rw [h]; ring) hfacne
  set badFor : (Fin ℓ → Fin m → ZMod 3) → Finset (Bits n) := fun c =>
    (Finset.univ : Finset (Bits n)).filter
      (fun x => Gad c x ≠ bit (decide (∃ i, q i x = 1))) with hbadFor
  -- for each input, few choices of the random coefficients are bad
  have hpoint : ∀ x : Bits n,
      ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
        (fun c => x ∈ badFor c)).card * 3 ^ ℓ ≤ 3 ^ (m * ℓ) := by
    intro x
    by_cases hx : ∃ i, q i x = 1
    · obtain ⟨i₀, hi₀⟩ := hx
      have hbit : bit (decide (∃ i, q i x = 1)) = 1 := by
        have : (∃ i, q i x = 1) := ⟨i₀, hi₀⟩
        simp [this]
      have hsub : ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
            (fun c => x ∈ badFor c))
          ⊆ (Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
            (fun c => ∀ j, (∑ i, c j i * q i x) = 0) := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbadFor] at hc ⊢
        intro j
        rw [← hSval]
        refine hne c x ?_ j
        rw [hbit] at hc
        exact hc
      have hker := card_kernel_mul (fun i => q i x) i₀ hi₀
      have hrows := card_rows_filter (m := m) (ℓ := ℓ) (fun v => (∑ i, v i * q i x) = 0)
      calc ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
            (fun c => x ∈ badFor c)).card * 3 ^ ℓ
          ≤ ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
              (fun c => ∀ j, (∑ i, c j i * q i x) = 0)).card * 3 ^ ℓ :=
            Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
        _ = ((Finset.univ : Finset (Fin m → ZMod 3)).filter
              (fun v => (∑ i, v i * q i x) = 0)).card ^ ℓ * 3 ^ ℓ := by rw [hrows]
        _ = (3 * ((Finset.univ : Finset (Fin m → ZMod 3)).filter
              (fun v => (∑ i, v i * q i x) = 0)).card) ^ ℓ := by
            rw [mul_pow]; ring
        _ = (3 ^ m) ^ ℓ := by rw [hker]
        _ = 3 ^ (m * ℓ) := by rw [← pow_mul]
    · push_neg at hx
      have h0 : ∀ i, q i x = 0 := by
        intro i
        rcases hq01 i x with h | h
        · exact h
        · exact absurd h (hx i)
      have hempty : ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
          (fun c => x ∈ badFor c)) = ∅ := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, hbadFor]
        intro hc
        apply hc
        rw [hzero c x h0]
        have : ¬ (∃ i, q i x = 1) := by
          rintro ⟨i, hi⟩
          exact hx i hi
        simp [this]
      rw [hempty]
      simp
  -- averaging over the random coefficients
  have hswap : ∑ c : (Fin ℓ → Fin m → ZMod 3), (badFor c).card
      = ∑ x : Bits n, ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
          (fun c => x ∈ badFor c)).card := by
    simp only [hbadFor, Finset.card_filter, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.sum_comm]
  have hcardc : (Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).card = 3 ^ (m * ℓ) := by
    simp [Finset.card_univ, ZMod.card, pow_mul]
  have hsum : ∑ c : (Fin ℓ → Fin m → ZMod 3), (badFor c).card * 3 ^ ℓ
      ≤ ∑ _c : (Fin ℓ → Fin m → ZMod 3), 2 ^ n := by
    calc ∑ c : (Fin ℓ → Fin m → ZMod 3), (badFor c).card * 3 ^ ℓ
        = (∑ c : (Fin ℓ → Fin m → ZMod 3), (badFor c).card) * 3 ^ ℓ := by rw [Finset.sum_mul]
      _ = (∑ x : Bits n, ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
            (fun c => x ∈ badFor c)).card) * 3 ^ ℓ := by rw [hswap]
      _ = ∑ x : Bits n, (((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
            (fun c => x ∈ badFor c)).card * 3 ^ ℓ) := by rw [Finset.sum_mul]
      _ ≤ ∑ _x : Bits n, 3 ^ (m * ℓ) := Finset.sum_le_sum (fun x _ => hpoint x)
      _ = 2 ^ n * 3 ^ (m * ℓ) := by
          simp [Finset.sum_const, Finset.card_univ]
      _ = ∑ _c : (Fin ℓ → Fin m → ZMod 3), 2 ^ n := by
          rw [Finset.sum_const, hcardc, smul_eq_mul, mul_comm]
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨Gad c₀, hdeg c₀, hval01 c₀, hc₀⟩

