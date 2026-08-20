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

theorem parity_not_ac0 : ¬ InAC0 parity := by
  rintro ⟨d, c, hC⟩
  obtain ⟨i, hi⟩ := exists_two_pow_dominates (2 * c + 4) (2 * d) 144
  set m : ℕ := 2 ^ i with hm
  set l : ℕ := c * (i + 2) + 2 with hl
  set D : ℕ := (2 * l) ^ d with hD
  have hl1 : 1 ≤ l := by omega
  -- The polynomial bound on the circuit size is beaten by `3 ^ l`.
  have hF1 : 4 * (2 * m + 2) ^ c ≤ 3 ^ l := by
    have h1 : 2 * m + 2 ≤ 3 ^ (i + 2) := by
      calc 2 * m + 2 = 2 ^ (i + 1) + 2 := by rw [hm, pow_succ]; ring
        _ ≤ 2 ^ (i + 1) + 2 ^ (i + 1) := by
            have : (2:ℕ) ≤ 2 ^ (i + 1) := by
              calc (2:ℕ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
        _ = 2 ^ (i + 2) := by ring
        _ ≤ 3 ^ (i + 2) := Nat.pow_le_pow_left (by norm_num) _
    calc 4 * (2 * m + 2) ^ c ≤ 9 * (3 ^ (i + 2)) ^ c := by
          exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left h1 c)
      _ = 3 ^ (c * (i + 2) + 2) := by rw [← pow_mul]; ring
      _ = 3 ^ l := by rw [hl]
  -- The degree bound is beaten by `√(3m)`.
  have hF2 : 16 * (D + 2) ^ 2 ≤ 3 * m := by
    have hQ1 : 1 ≤ ((2 * c + 4) * (i + 2)) ^ d := Nat.one_le_pow _ _ (by positivity)
    have hDQ : D ≤ ((2 * c + 4) * (i + 2)) ^ d := by
      rw [hD]
      exact Nat.pow_le_pow_left (by rw [hl]; nlinarith) d
    have h3Q : D + 2 ≤ 3 * ((2 * c + 4) * (i + 2)) ^ d := by omega
    calc 16 * (D + 2) ^ 2 ≤ 16 * (3 * ((2 * c + 4) * (i + 2)) ^ d) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3Q 2)
      _ = 144 * (((2 * c + 4) * (i + 2)) ^ d) ^ 2 := by ring
      _ = 144 * ((2 * c + 4) * (i + 2)) ^ (2 * d) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ i := hi
      _ ≤ 3 * m := by rw [hm]; omega
  -- The circuit computing parity on `2m` bits.
  obtain ⟨C, hdepth, hsize, heval⟩ := hC (2 * m)
  obtain ⟨f, hfDeg, -, hfbad⟩ := exists_approx l hl1 C
  have hfDeg' : f ∈ Deg (2 * m) D := by
    refine Deg_mono ?_ hfDeg
    rw [hD]
    exact Nat.pow_le_pow_right (by omega) hdepth
  -- The set of inputs where the approximation is correct.
  have hbadeq : (Finset.univ.filter (fun x : Bits (2 * m) => f x ≠ bit (C.eval x)))
      = Finset.univ.filter (fun x : Bits (2 * m) => ¬ (f x = bit (parity (2 * m) x))) := by
    apply Finset.filter_congr
    intro x _
    rw [heval x]
  set bad := Finset.univ.filter (fun x : Bits (2 * m) => ¬ (f x = bit (parity (2 * m) x)))
    with hbad
  set G := Finset.univ.filter (fun x : Bits (2 * m) => f x = bit (parity (2 * m) x)) with hGdef
  have hpart : G.card + bad.card = 2 ^ (2 * m) := by
    rw [hGdef, hbad, Finset.card_filter_add_card_filter_not]
    simp
  have h4bad : 4 * bad.card ≤ 2 ^ (2 * m) := by
    rw [hbadeq] at hfbad
    have hb : bad.card * 3 ^ l ≤ C.size * 2 ^ (2 * m) := hfbad
    have key : (4 * bad.card) * 3 ^ l ≤ 2 ^ (2 * m) * 3 ^ l := by
      calc (4 * bad.card) * 3 ^ l = 4 * (bad.card * 3 ^ l) := by ring
        _ ≤ 4 * (C.size * 2 ^ (2 * m)) := Nat.mul_le_mul_left _ hb
        _ = (4 * C.size) * 2 ^ (2 * m) := by ring
        _ ≤ (4 * (2 * m + 2) ^ c) * 2 ^ (2 * m) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsize)
        _ ≤ 3 ^ l * 2 ^ (2 * m) := Nat.mul_le_mul_right _ hF1
        _ = 2 ^ (2 * m) * 3 ^ l := by ring
    exact Nat.le_of_mul_le_mul_right key (by positivity)
  have h3G : 3 * 2 ^ (2 * m) ≤ 4 * G.card := by omega
  -- Smolensky's bound.
  have hgmem : (1 + f) ∈ Deg (2 * m) D := Submodule.add_mem _ one_mem_Deg hfDeg'
  have hgG : ∀ x ∈ G, (1 + f) x = sgn (parity (2 * m) x) := by
    intro x hx
    rw [hGdef, Finset.mem_filter] at hx
    rw [Pi.add_apply, Pi.one_apply, hx.2, ← sgn_eq]
  have hsm := smolensky_card_le (n := 2 * m) (D := D) (K := m + (D + 1)) (by omega) G (1 + f)
    hgmem hgG
  have hcount := card_subsets_le m (D + 1)
  set N := ((Finset.univ : Finset (Finset (Fin (2 * m)))).filter
    (fun T => T.card ≤ m + (D + 1))).card with hN
  set C0 := Nat.centralBinom m with hC0
  -- Arithmetic contradiction.
  have hpow : (2:ℕ) ^ (2 * m) = 4 ^ m := by
    rw [pow_mul]; norm_num
  have hcount' : 2 * N ≤ 4 ^ m + 2 * ((D + 2) * C0) := by
    calc 2 * N ≤ 4 ^ m + 2 * (D + 1 + 1) * C0 := hcount
      _ = 4 ^ m + 2 * ((D + 2) * C0) := by ring
  have hXY : 4 ^ m ≤ 4 * ((D + 2) * C0) := by
    rw [hpow] at h3G
    omega
  have hC0pos : 0 < C0 := Nat.centralBinom_pos m
  have h1 : (4 ^ m : ℕ) ^ 2 ≤ (4 * ((D + 2) * C0)) ^ 2 := Nat.pow_le_pow_left hXY 2
  have h2 : (4 * ((D + 2) * C0)) ^ 2 = (16 * (D + 2) ^ 2) * C0 ^ 2 := by ring
  have h3 : (16 * (D + 2) ^ 2) * C0 ^ 2 ≤ (3 * m) * C0 ^ 2 :=
    Nat.mul_le_mul_right _ hF2
  have h4 : (3 * m) * C0 ^ 2 < (3 * m + 1) * C0 ^ 2 := by
    have : 0 < C0 ^ 2 := by positivity
    nlinarith
  have h5 : C0 ^ 2 * (3 * m + 1) ≤ 16 ^ m := centralBinom_sq_mul_le m
  have h6 : ((4:ℕ) ^ m) ^ 2 = 16 ^ m := by
    rw [← pow_mul, mul_comm m 2, pow_mul]; norm_num
  rw [h6] at h1
  rw [h2] at h1
  have : (16:ℕ) ^ m < 16 ^ m := by
    calc (16:ℕ) ^ m ≤ (16 * (D + 2) ^ 2) * C0 ^ 2 := h1
      _ ≤ (3 * m) * C0 ^ 2 := h3
      _ < (3 * m + 1) * C0 ^ 2 := h4
      _ = C0 ^ 2 * (3 * m + 1) := by ring
      _ ≤ 16 ^ m := h5
  exact absurd this (lt_irrefl _)

end CS

