import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Setup

We work with 7 qubits.  The computational basis of the state space is indexed by
`V2 = Fin 7 → ZMod 2` (bit strings of length 7), and a state is a function `Ket = V2 → ℂ`.

For `a b : V2` the Pauli operator `pauli a b` acts on basis kets by
`P(a,b) |v⟩ = (-1)^(b ⬝ v) |v + a⟩`; thus `pauli a 0` is a product of `X`'s on the support of
`a`, `pauli 0 b` a product of `Z`'s on the support of `b`, and `pauli a b` with `a = b`
supported on one qubit is `Y` on that qubit (up to the irrelevant global phase `i`).

The Steane code is the CSS code built from the `[7,4,3]` Hamming code: the two logical basis
states `u 0`, `u 1` are the uniform superpositions over the two cosets of the dual Hamming
code `C₂` (the `[7,3,4]` simplex code) inside the Hamming code.

The theorem `QI.steane_code` states the Knill–Laflamme error-correction conditions for the
set of *all* single-qubit Pauli errors, together with the fact that the two logical basis
states are orthogonal and nonzero (so the code space really is two-dimensional).
Since `⟪E u_i, F u_j⟫ = ⟪u_i, E† F u_j⟫`, the second conjunct is literally the
Knill–Laflamme condition `P E† F P = c_{E,F} · P` for the projector `P` onto the code space,
which is necessary and sufficient for the existence of a recovery channel correcting every
single-qubit error.
-/

/-- Bit strings of length 7 (indices of the computational basis of 7 qubits). -/
abbrev V2 := Fin 7 → ZMod 2

/-- A state of the 7 qubits, given by its computational-basis amplitudes. -/
abbrev Ket := V2 → ℂ

/-- The sign character `(-1) ^ x` of `ZMod 2`, valued in `ℂ`. -/
def eps (x : ZMod 2) : ℂ := if x = 0 then 1 else -1

/-- The `ZMod 2`-valued inner product of two bit strings. -/
def dot (a b : V2) : ZMod 2 := ∑ i, a i * b i

/-- The all-ones bit string; it implements the logical `X` of the Steane code. -/
def tvec : V2 := ![1, 1, 1, 1, 1, 1, 1]

/-- The dual Hamming code `C₂ = C₁^⊥` (the `[7,3,4]` simplex code): all 8 linear
combinations of the three rows of the Hamming parity-check matrix. -/
def C2 : Finset V2 :=
  {![0,0,0,0,0,0,0], ![1,0,1,0,1,0,1], ![0,1,1,0,0,1,1], ![0,0,0,1,1,1,1],
   ![1,1,0,0,1,1,0], ![1,0,1,1,0,1,0], ![0,1,1,1,1,0,0], ![1,1,0,1,0,0,1]}

/-- The coset representative used for the logical basis state `i`. -/
def shift : Fin 2 → V2 := fun i => if i = 0 then 0 else tvec

/-- The support of the `i`-th logical basis state: the coset `C₂ + shift i`. -/
def code (i : Fin 2) : Finset V2 := C2.image (· + shift i)

/-- The logical basis states `|0_L⟩` and `|1_L⟩` of the Steane code (unnormalised: each is a
sum of 8 computational basis states). -/
def u (i : Fin 2) : Ket := fun w => if w ∈ code i then 1 else 0

/-- The Hermitian inner product on `Ket`. -/
noncomputable def inner' (f g : Ket) : ℂ := ∑ w, (starRingEnd ℂ) (f w) * g w

/-- The Pauli operator `P(a,b)`, acting on basis kets by `P(a,b) |v⟩ = (-1)^(b ⬝ v) |v + a⟩`. -/
def pauli (a b : V2) : Ket →ₗ[ℂ] Ket where
  toFun f := fun w => eps (dot b (w + a)) * f (w + a)
  map_add' f g := by funext w; simp [mul_add]
  map_smul' r f := by funext w; simp [Pi.smul_apply]; ring

/-- `a` and `b` are supported on a single (common) qubit: `pauli a b` is then an arbitrary
single-qubit Pauli error (identity, `X`, `Z` or `Y` on some qubit `q`). -/
def SingleQubit (a b : V2) : Prop := ∃ q : Fin 7, ∀ j, j ≠ q → a j = 0 ∧ b j = 0

/-- A vector supported on at most two qubits. -/
def Wt2 (p : V2) : Prop := ∃ q q' : Fin 7, ∀ j, j ≠ q → j ≠ q' → p j = 0

/-! ## Elementary lemmas -/

lemma eps_zero : eps 0 = 1 := rfl

lemma eps_add (x y : ZMod 2) : eps (x + y) = eps x * eps y := by
  fin_cases x <;> fin_cases y <;>
    norm_num [eps, show ((1 : ZMod 2) + 1) = 0 from by decide]

lemma eps_conj (x : ZMod 2) : (starRingEnd ℂ) (eps x) = eps x := by
  fin_cases x <;> simp [eps]

lemma dot_add_right (a b c : V2) : dot a (b + c) = dot a b + dot a c := by
  simp only [dot, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

lemma dot_add_left (a b c : V2) : dot (a + b) c = dot a c + dot b c := by
  simp only [dot, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

lemma dot_zero_left (a : V2) : dot 0 a = 0 := by simp [dot]

lemma dot_zero_right (a : V2) : dot a 0 = 0 := by simp [dot]

lemma add_self_v2 (a : V2) : a + a = 0 := by
  funext i; simp [CharTwo.add_self_eq_zero]

lemma add_cancel_v2 (a b : V2) : a + b + b = a := by
  rw [add_assoc, add_self_v2, add_zero]

/-! ## Combinatorial facts about the Steane code -/

lemma C2_add_mem : ∀ c ∈ C2, ∀ d ∈ C2, c + d ∈ C2 := by decide

lemma C2_card : C2.card = 8 := by decide

lemma C2_add_iff {c x : V2} (hc : c ∈ C2) : c + x ∈ C2 ↔ x ∈ C2 := by
  constructor
  · intro h
    have := C2_add_mem c hc _ h
    rwa [← add_assoc, add_self_v2, zero_add] at this
  · intro h; exact C2_add_mem c hc x h

lemma wt2_of_single {a b a' b' : V2} (h : SingleQubit a b) (h' : SingleQubit a' b') :
    Wt2 (a + a') ∧ Wt2 (b + b') := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨q', hq'⟩ := h'
  refine ⟨⟨q, q', ?_⟩, ⟨q, q', ?_⟩⟩ <;> intro j h1 h2 <;>
    simp [(hq j h1).1, (hq j h1).2, (hq' j h2).1, (hq' j h2).2]

/-- The simplex code has minimum weight 4: a codeword of weight ≤ 2 is zero. -/
lemma C2_min_weight : ∀ p : V2, p ∈ C2 → Wt2 p → p = 0 := by
  unfold Wt2; decide

/-- The nontrivial coset `C₂ + t` has minimum weight 3. -/
lemma C2_coset_min_weight : ∀ p : V2, Wt2 p → p + tvec ∉ C2 := by
  unfold Wt2 tvec; decide

/-- The Hamming code has distance 3: a vector of weight ≤ 2 which is not orthogonal to the
all-ones vector fails to be orthogonal to some element of `C₂`. -/
lemma hamming_min_weight : ∀ s : V2, Wt2 s → dot s tvec = 1 → ∃ c ∈ C2, dot s c = 1 := by
  unfold Wt2 dot tvec; decide

/-! ## The character sum over `C₂` -/

/-- If `s` is not orthogonal to `C₂`, the character sum over `C₂` vanishes. -/
lemma char_sum_eq_zero {s : V2} (h : ∃ c ∈ C2, dot s c = 1) :
    ∑ c ∈ C2, eps (dot s c) = 0 := by
  obtain ⟨c0, hc0, hdot⟩ := h
  have key : ∑ c ∈ C2, eps (dot s c) = - ∑ c ∈ C2, eps (dot s c) := by
    calc ∑ c ∈ C2, eps (dot s c)
        = ∑ c ∈ C2, eps (dot s (c + c0)) := by
          refine (Finset.sum_nbij' (fun c => c + c0) (fun c => c + c0) ?_ ?_ ?_ ?_ ?_).symm
          · intro c hc; exact C2_add_mem c hc c0 hc0
          · intro c hc; exact C2_add_mem c hc c0 hc0
          · intro c _; exact add_cancel_v2 c c0
          · intro c _; exact add_cancel_v2 c c0
          · intro c _; rfl
      _ = - ∑ c ∈ C2, eps (dot s c) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [dot_add_right, hdot, eps_add]
          simp [eps]
  have h2 : (2 : ℂ) * ∑ c ∈ C2, eps (dot s c) = 0 := by linear_combination key
  simpa using h2

/-! ## The main computation -/

lemma mem_code_iff (v : V2) (j : Fin 2) : v ∈ code j ↔ v + shift j ∈ C2 := by
  simp only [code, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rwa [add_cancel_v2]
  · intro h
    exact ⟨v + shift j, h, add_cancel_v2 v (shift j)⟩

lemma u_conj (i : Fin 2) (v : V2) : (starRingEnd ℂ) (u i v) = u i v := by
  unfold u; split <;> simp

lemma inner_pauli (a b a' b' : V2) (i j : Fin 2) :
    inner' (pauli a b (u i)) (pauli a' b' (u j))
      = eps (dot b' (a + a')) *
        ∑ c ∈ C2, eps (dot (b + b') (c + shift i)) * u j (c + shift i + (a + a')) := by
  have hre : ∀ F : V2 → ℂ, ∑ w, F w = ∑ v, F (v + a) :=
    fun F => (Fintype.sum_equiv (Equiv.addRight a) _ _ (fun v => rfl)).symm
  have step1 : inner' (pauli a b (u i)) (pauli a' b' (u j))
      = ∑ v : V2, eps (dot (b + b') v) * u i v *
          (eps (dot b' (a + a')) * u j (v + (a + a'))) := by
    rw [inner']
    rw [hre]
    refine Finset.sum_congr rfl fun v _ => ?_
    show (starRingEnd ℂ) (eps (dot b (v + a + a)) * u i (v + a + a)) *
      (eps (dot b' (v + a + a')) * u j (v + a + a')) = _
    rw [add_cancel_v2 v a]
    have hva : v + a + a' = v + (a + a') := by rw [add_assoc]
    rw [hva]
    rw [map_mul, eps_conj, u_conj]
    rw [dot_add_right b' v (a + a'), eps_add, dot_add_left b b' v, eps_add]
    ring
  have step2 : ∑ v : V2, eps (dot (b + b') v) * u i v *
      (eps (dot b' (a + a')) * u j (v + (a + a')))
      = eps (dot b' (a + a')) * ∑ v : V2, eps (dot (b + b') v) * u i v *
          u j (v + (a + a')) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  -- reduce the sum over all `v` to a sum over `C₂`
  have step3 : ∑ v : V2, eps (dot (b + b') v) * u i v * u j (v + (a + a'))
      = ∑ c ∈ C2, eps (dot (b + b') (c + shift i)) * u j (c + shift i + (a + a')) := by
    have hsplit : ∑ v : V2, eps (dot (b + b') v) * u i v * u j (v + (a + a'))
        = ∑ v : V2, if v ∈ code i then
            eps (dot (b + b') v) * u j (v + (a + a')) else 0 := by
      refine Finset.sum_congr rfl fun v _ => ?_
      unfold u
      by_cases hv : v ∈ code i <;> simp [hv]
    rw [hsplit, Finset.sum_ite_mem, Finset.univ_inter]
    rw [code, Finset.sum_image (by intro x _ y _ h; exact add_right_cancel h)]
  rw [step1, step2, step3]

/-! ## The Knill–Laflamme conditions -/

lemma inner_offdiag {a b a' b' : V2} (hp : Wt2 (a + a')) {i j : Fin 2} (hij : i ≠ j) :
    inner' (pauli a b (u i)) (pauli a' b' (u j)) = 0 := by
  rw [inner_pauli]
  have hterm : ∀ c ∈ C2, eps (dot (b + b') (c + shift i)) * u j (c + shift i + (a + a')) = 0 := by
    intro c hc
    have hnot : c + shift i + (a + a') ∉ code j := by
      rw [mem_code_iff]
      intro hmem
      have hst : shift i + shift j = tvec := by
        fin_cases i <;> fin_cases j <;> simp_all [shift]
      have : c + ((a + a') + tvec) ∈ C2 := by
        have hre : c + shift i + (a + a') + shift j = c + ((a + a') + (shift i + shift j)) := by
          abel
        rw [hre, hst] at hmem
        exact hmem
      rw [C2_add_iff hc] at this
      exact C2_coset_min_weight (a + a') hp this
    unfold u
    simp [hnot]
  rw [Finset.sum_congr rfl hterm]
  simp

lemma inner_diag {a b a' b' : V2} (hp : Wt2 (a + a')) (i : Fin 2) :
    inner' (pauli a b (u i)) (pauli a' b' (u i))
      = if a = a' then eps (dot (b + b') (shift i)) * ∑ c ∈ C2, eps (dot (b + b') c) else 0 := by
  rw [inner_pauli]
  by_cases hpz : a + a' = 0
  · have haa : a = a' := by
      have := congrArg (· + a') hpz
      simpa [add_cancel_v2] using this
    subst haa
    have hz : a + a = (0 : V2) := add_self_v2 a
    rw [hz]
    have hterm : ∀ c ∈ C2, eps (dot (b + b') (c + shift i)) * u i (c + shift i + 0)
        = eps (dot (b + b') (shift i)) * eps (dot (b + b') c) := by
      intro c hc
      have hmem : c + shift i + 0 ∈ code i := by
        rw [mem_code_iff, add_zero, add_cancel_v2]
        exact hc
      unfold u
      rw [if_pos hmem, mul_one, dot_add_right, eps_add]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    simp [dot_zero_right, eps_zero]
  · have hne : a ≠ a' := by
      intro h; apply hpz; rw [h]; exact add_self_v2 a'
    have hterm : ∀ c ∈ C2, eps (dot (b + b') (c + shift i)) * u i (c + shift i + (a + a')) = 0 := by
      intro c hc
      have hnot : c + shift i + (a + a') ∉ code i := by
        rw [mem_code_iff]
        intro hmem
        have hst : shift i + shift i = (0 : V2) := add_self_v2 _
        have hre : c + shift i + (a + a') + shift i = c + ((a + a') + (shift i + shift i)) := by
          abel
        rw [hre, hst, add_zero, C2_add_iff hc] at hmem
        exact hpz (C2_min_weight _ hmem hp)
      unfold u
      simp [hnot]
    rw [Finset.sum_congr rfl hterm]
    simp [hne]

/-- Every single-qubit Pauli operator on qubit `q` (namely `I`, `X`, `Z` and, up to a global
phase, `Y`, according to the values of `x` and `z`) belongs to the error set. -/
lemma singleQubit_pauli (q : Fin 7) (x z : ZMod 2) :
    SingleQubit (fun j => if j = q then x else 0) (fun j => if j = q then z else 0) :=
  ⟨q, fun j hj => by simp [hj]⟩

/-- **The Steane code corrects any single-qubit error.**

The first conjunct says that the two logical basis states `u 0 = |0_L⟩` and `u 1 = |1_L⟩` are
orthogonal and nonzero, so the code space is two-dimensional.

The second conjunct is the Knill–Laflamme condition for the set of all single-qubit Pauli
errors `E = pauli a b`, `F = pauli a' b'` (`a`, `b` supported on a single qubit, and likewise
`a'`, `b'`): for each such pair there is a constant `c` with
`⟪u i, E† F u j⟫ = ⟪E u i, F u j⟫ = c · δ_{ij}`.  By the Knill–Laflamme theorem this is
necessary and sufficient for the existence of a recovery operation correcting an arbitrary
error acting on a single one of the seven qubits. -/
theorem steane_code :
    (∀ i j : Fin 2, inner' (u i) (u j) = if i = j then 8 else 0) ∧
    (∀ a b a' b' : V2, SingleQubit a b → SingleQubit a' b' →
      ∃ c : ℂ, ∀ i j : Fin 2,
        inner' (pauli a b (u i)) (pauli a' b' (u j)) = if i = j then c else 0) := by
  have hpauli0 : ∀ f : Ket, pauli 0 0 f = f := by
    intro f
    funext w
    show eps (dot 0 (w + 0)) * f (w + 0) = f w
    simp [dot_zero_left, eps_zero]
  have hwt0 : Wt2 (0 : V2) := ⟨0, 0, fun j _ _ => rfl⟩
  constructor
  · intro i j
    rw [show u i = pauli 0 0 (u i) from (hpauli0 _).symm,
        show u j = pauli 0 0 (u j) from (hpauli0 _).symm]
    by_cases hij : i = j
    · subst hij
      rw [inner_diag (by simpa using hwt0) i, if_pos rfl]
      have : ∀ c ∈ C2, eps (dot ((0 : V2) + 0) c) = 1 := by
        intro c _; simp [dot_zero_left, eps_zero]
      rw [Finset.sum_congr rfl this]
      simp [dot_zero_left, eps_zero, C2_card]
    · rw [inner_offdiag (by simpa using hwt0) hij, if_neg hij]
  · intro a b a' b' h h'
    obtain ⟨hp, hs⟩ := wt2_of_single h h'
    refine ⟨if a = a' then eps (dot (b + b') (shift 0)) * ∑ c ∈ C2, eps (dot (b + b') c) else 0,
      ?_⟩
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [inner_diag hp i, if_pos rfl]
      by_cases haa : a = a'
      · rw [if_pos haa, if_pos haa]
        by_cases hst : dot (b + b') tvec = 0
        · have h0 : eps (dot (b + b') (shift i)) = eps (dot (b + b') (shift 0)) := by
            fin_cases i
            · rfl
            · show eps (dot (b + b') tvec) = eps (dot (b + b') 0)
              rw [hst, dot_zero_right]
          rw [h0]
        · have h1 : dot (b + b') tvec = 1 := by
            revert hst
            generalize dot (b + b') tvec = x
            fin_cases x <;> simp
          have : ∑ c ∈ C2, eps (dot (b + b') c) = 0 :=
            char_sum_eq_zero (hamming_min_weight _ hs h1)
          rw [this]
          ring
      · rw [if_neg haa, if_neg haa]
    · rw [inner_offdiag hp hij, if_neg hij]

end QI

