import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

theorem exists_depth_two_circuit (n : ℕ) (f : Cube n → Bool) :
    ∃ c : Circuit n, c.DepthLe 2 ∧ c.Computes f := by
  classical
  have hcard : Fintype.card (Cube n) = 2 ^ n := by simp [Cube]
  set e : Cube n ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq hcard with he
  have hout : 2 * n + 2 ^ n < 2 * n + 2 ^ n + 1 := by omega
  -- the gates a gate refers to come earlier, and sit in an earlier layer
  have hrefs : ∀ i : Fin (2 * n + 2 ^ n + 1), ∀ j ∈ (dgate f e i).refs,
      (j : ℕ) < (i : ℕ) := by
    intro i j hj
    by_cases h1 : (i : ℕ) < n
    · rw [dgate_var f e i h1] at hj; simp [Gate.refs] at hj
    · by_cases h2 : (i : ℕ) < 2 * n
      · rw [dgate_not f e i h1 h2] at hj
        simp only [Gate.refs, Finset.mem_singleton] at hj
        subst hj
        show (i : ℕ) - n < (i : ℕ)
        omega
      · by_cases h3 : (i : ℕ) < 2 * n + 2 ^ n
        · rw [dgate_and f e i h1 h2 h3] at hj
          simp only [Gate.refs] at hj
          obtain ⟨k, rfl⟩ := mem_lits hj
          have hlt := litIdx_lt (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩) k
          show litIdx _ k < (i : ℕ)
          omega
        · rw [dgate_or f e i h1 h2 h3] at hj
          simp only [Gate.refs, terms, Finset.mem_image, Finset.mem_filter] at hj
          obtain ⟨k, -, rfl⟩ := hj
          have hk := k.2
          have hi : (i : ℕ) = 2 * n + 2 ^ n := by have := i.2; omega
          show 2 * n + (k : ℕ) < (i : ℕ)
          omega
  refine ⟨⟨2 * n + 2 ^ n + 1, dgate f e, ⟨2 * n + 2 ^ n, hout⟩, hrefs⟩, ?_, ?_⟩
  · -- depth 2
    refine ⟨fun i => if (i : ℕ) < 2 * n then 0 else if (i : ℕ) < 2 * n + 2 ^ n then 1 else 2,
      fun i => by dsimp only; split <;> [omega; split] <;> omega, ?_⟩
    intro i j hj
    have hj0 : j ∈ (dgate f e i).refs := hj
    have hji := hrefs i j hj0
    dsimp only
    by_cases h1 : (i : ℕ) < n
    · rw [dgate_var f e i h1] at hj0; simp [Gate.refs] at hj0
    · by_cases h2 : (i : ℕ) < 2 * n
      · have e1 : (if (j : ℕ) < 2 * n then 0 else
            if (j : ℕ) < 2 * n + 2 ^ n then 1 else 2) = 0 := if_pos (by omega)
        have e2 : (if (i : ℕ) < 2 * n then 0 else
            if (i : ℕ) < 2 * n + 2 ^ n then 1 else 2) = 0 := if_pos h2
        rw [dgate_not f e i h1 h2]
        simp only [Gate.cost]
        omega
      · by_cases h3 : (i : ℕ) < 2 * n + 2 ^ n
        · rw [dgate_and f e i h1 h2 h3] at hj0 ⊢
          simp only [Gate.refs] at hj0
          obtain ⟨k, rfl⟩ := mem_lits hj0
          have hlt := litIdx_lt (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩) k
          have hcoe : ((lit (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩) k :
              Fin (2 * n + 2 ^ n + 1)) : ℕ) = litIdx (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩) k := rfl
          have e1 : (if ((lit (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩) k :
              Fin (2 * n + 2 ^ n + 1)) : ℕ) < 2 * n then 0 else
              if ((lit (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩) k :
                Fin (2 * n + 2 ^ n + 1)) : ℕ) < 2 * n + 2 ^ n then 1 else 2) = 0 :=
            if_pos (by rw [hcoe]; omega)
          have e2 : (if (i : ℕ) < 2 * n then 0 else
              if (i : ℕ) < 2 * n + 2 ^ n then 1 else 2) = 1 := by
            rw [if_neg h2, if_pos h3]
          simp only [Gate.cost]
          omega
        · rw [dgate_or f e i h1 h2 h3] at hj0 ⊢
          simp only [Gate.refs, terms, Finset.mem_image, Finset.mem_filter] at hj0
          obtain ⟨k, -, rfl⟩ := hj0
          have hk := k.2
          have hcoe : ((term k : Fin (2 * n + 2 ^ n + 1)) : ℕ) = 2 * n + (k : ℕ) := rfl
          have e1 : (if ((term k : Fin (2 * n + 2 ^ n + 1)) : ℕ) < 2 * n then 0 else
              if ((term k : Fin (2 * n + 2 ^ n + 1)) : ℕ) < 2 * n + 2 ^ n then 1 else 2) = 1 := by
            rw [if_neg (by rw [hcoe]; omega), if_pos (by rw [hcoe]; omega)]
          have e2 : (if (i : ℕ) < 2 * n then 0 else
              if (i : ℕ) < 2 * n + 2 ^ n then 1 else 2) = 2 := by
            rw [if_neg h2, if_neg h3]
          simp only [Gate.cost]
          omega
  · -- semantics
    intro x
    refine ⟨dval f e x, ?_, ?_⟩
    · intro i
      show dval f e x i = Gate.eval x (dval f e x) (dgate f e i)
      by_cases h1 : (i : ℕ) < n
      · rw [dgate_var f e i h1, dval_var f e x i h1]
        rfl
      · by_cases h2 : (i : ℕ) < 2 * n
        · rw [dgate_not f e i h1 h2, dval_not f e x i h1 h2]
          simp only [Gate.eval]
          rw [dval_var f e x ⟨(i : ℕ) - n, by omega⟩ (by show (i : ℕ) - n < n; omega)]
        · by_cases h3 : (i : ℕ) < 2 * n + 2 ^ n
          · rw [dgate_and f e i h1 h2 h3, dval_and f e x i h1 h2 h3]
            set a : Cube n := e.symm ⟨(i : ℕ) - 2 * n, by omega⟩ with ha
            simp only [Gate.eval]
            congr 1
            simp only [eq_iff_iff]
            constructor
            · rintro rfl j hj
              obtain ⟨k, rfl⟩ := mem_lits hj
              rw [dval_lit]
              by_cases hak : a k <;> simp [hak]
            · intro h
              funext k
              have hk := h (lit a k) (lit_mem a k)
              rw [dval_lit] at hk
              by_cases hak : a k <;> simp [hak] at hk <;> simp [hak, hk]
          · rw [dgate_or f e i h1 h2 h3, dval_or f e x i h1 h2 h3]
            simp only [Gate.eval]
            by_cases hfx : f x = true
            · have hmem : term (e x) ∈ terms f e :=
                Finset.mem_image.mpr ⟨e x, by simp [hfx], rfl⟩
              have hex : ∃ j ∈ terms f e, dval f e x j = true := by
                refine ⟨term (e x), hmem, ?_⟩
                rw [dval_term]
                simp
              rw [hfx, decide_eq_true hex]
            · have hno : ¬ ∃ j ∈ terms f e, dval f e x j = true := by
                rintro ⟨j, hjmem, hjval⟩
                simp only [terms, Finset.mem_image, Finset.mem_filter] at hjmem
                obtain ⟨k, ⟨-, hk⟩, rfl⟩ := hjmem
                rw [dval_term] at hjval
                have hxk : x = e.symm k := by simpa using hjval
                rw [← hxk] at hk
                exact hfx hk
              simp only [Bool.not_eq_true] at hfx
              rw [hfx, decide_eq_false hno]
    · show dval f e x ⟨2 * n + 2 ^ n, hout⟩ = f x
      rw [dval_or f e x ⟨2 * n + 2 ^ n, hout⟩ (by show ¬ (2 * n + 2 ^ n < n); omega)
        (by show ¬ (2 * n + 2 ^ n < 2 * n); omega) (by show ¬ (2 * n + 2 ^ n < 2 * n + 2 ^ n); omega)]

/-- Parity is computed by a (large) depth-2 circuit; the lower bound
`CS.parity_not_ac0` is therefore genuinely about circuit *size*. -/
