/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command, so the header above is written as a
-- plain block comment rather than a `/-!` module docstring.)

import Mathlib

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## The 9-qubit register

We label the nine qubits by `Site = Fin 3 × Fin 3`: the first coordinate is the *block*
(one of three three-qubit repetition blocks) and the second the position inside the block.
A computational basis state is a bit string `Bits = Site → ZMod 2`, and a state vector is
its amplitude function `Amp = Bits → ℂ`.
-/

abbrev Site : Type := Fin 3 × Fin 3

abbrev Bits : Type := Site → ZMod 2

abbrev Amp : Type := Bits → ℂ

/-- The Hermitian inner product `⟪u, v⟫ = ∑_b conj (u b) * v b`. -/
noncomputable def ipf (u v : Amp) : ℂ := ∑ b : Bits, (starRingEnd ℂ) (u b) * v b

/-- `sgn a = (-1)^a`. -/
def sgn (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

@[simp] lemma sgn_zero : sgn 0 = 1 := by simp [sgn]

@[simp] lemma sgn_one : sgn 1 = -1 := by
  simp [sgn, show (1 : ZMod 2) ≠ 0 from by decide]

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [show (1 + 1 : ZMod 2) = 0 from by decide]

lemma sgn_mul_self (a : ZMod 2) : sgn a * sgn a = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> simp

@[simp] lemma conj_sgn (a : ZMod 2) : (starRingEnd ℂ) (sgn a) = sgn a := by
  rcases zmod2_cases a with rfl | rfl <;> simp

/-! ## Bit strings -/

@[simp] lemma bits_add_self (b : Bits) : b + b = 0 := by
  funext p
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

lemma bits_add_add_cancel (b m : Bits) : b + m + m = b := by
  rw [add_assoc, bits_add_self, add_zero]

/-- The dot product of two bit strings, modulo 2. -/
def dot (z b : Bits) : ZMod 2 := ∑ p : Site, z p * b p

lemma dot_add_right (z b c : Bits) : dot z (b + c) = dot z b + dot z c := by
  simp only [dot, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

lemma dot_add_left (z w b : Bits) : dot (z + w) b = dot z b + dot w b := by
  simp only [dot, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

@[simp] lemma dot_zero_left (b : Bits) : dot 0 b = 0 := by simp [dot]

/-- The indicator bit string of a single qubit. -/
def e (q : Site) : Bits := fun p => if p = q then 1 else 0

@[simp] lemma dot_e (q : Site) (b : Bits) : dot (e q) b = b q := by
  simp [dot, e, Finset.sum_ite_eq' Finset.univ q]

lemma e_supp {q : Site} {p : Site} (h : e q p ≠ 0) : p = q := by
  by_contra hne
  exact h (by simp [e, hne])

/-! ## The Shor code space -/

/-- A basis label is a codeword label iff it is constant on each of the three blocks. -/
def isCode (b : Bits) : Prop := ∀ r s : Fin 3, b (r, s) = b (r, 0)

instance : DecidablePred isCode := fun b => by
  unfold isCode; infer_instance

/-- The bit string that repeats `c r` throughout block `r`. -/
def rep (c : Fin 3 → ZMod 2) : Bits := fun p => c p.1

/-- The block content of a bit string. -/
def blk (b : Bits) : Fin 3 → ZMod 2 := fun r => b (r, 0)

lemma isCode_rep (c : Fin 3 → ZMod 2) : isCode (rep c) := fun _ _ => rfl

lemma rep_blk {b : Bits} (hb : isCode b) : rep (blk b) = b := by
  funext p
  obtain ⟨r, s⟩ := p
  exact (hb r s).symm

@[simp] lemma blk_rep (c : Fin 3 → ZMod 2) : blk (rep c) = c := rfl

lemma rep_injective : Function.Injective rep := by
  intro c c' h
  have := congrArg blk h
  simpa using this

/-- Sums of functions supported on codeword labels reduce to sums over `Fin 3 → ZMod 2`. -/
lemma sum_over_code (f : Bits → ℂ) (hf : ∀ b, ¬ isCode b → f b = 0) :
    ∑ b : Bits, f b = ∑ c : Fin 3 → ZMod 2, f (rep c) := by
  have himg : ∑ b ∈ Finset.univ.image rep, f b = ∑ c : Fin 3 → ZMod 2, f (rep c) :=
    Finset.sum_image (fun x _ y _ h => rep_injective h)
  rw [← himg]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro b _ hb
  refine hf b ?_
  intro hcode
  exact hb (Finset.mem_image.2 ⟨blk b, Finset.mem_univ _, rep_blk hcode⟩)

/-- The normalisation constant `1 / (2√2)` of the Shor codewords. -/
noncomputable def kappa : ℂ := ((Real.sqrt 2 / 4 : ℝ) : ℂ)

@[simp] lemma conj_kappa : (starRingEnd ℂ) kappa = kappa := Complex.conj_ofReal _

lemma kappa_sq : kappa * kappa = 1 / 8 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [kappa, ← Complex.ofReal_mul]
  rw [show Real.sqrt 2 / 4 * (Real.sqrt 2 / 4) = Real.sqrt 2 * Real.sqrt 2 / 16 by ring, h]
  norm_num

/-- The parity of the block content. -/
def lw (b : Bits) : ZMod 2 := ∑ r : Fin 3, b (r, 0)

/-- The logical zero of the Shor code:
`|0_L⟩ = (1/2√2) (|000⟩+|111⟩)(|000⟩+|111⟩)(|000⟩+|111⟩)`. -/
noncomputable def zeroL : Amp := fun b => if isCode b then kappa else 0

/-- The logical one of the Shor code:
`|1_L⟩ = (1/2√2) (|000⟩-|111⟩)(|000⟩-|111⟩)(|000⟩-|111⟩)`. -/
noncomputable def oneL : Amp := fun b => if isCode b then sgn (lw b) * kappa else 0

lemma zeroL_off {b : Bits} (hb : ¬ isCode b) : zeroL b = 0 := by simp [zeroL, hb]

lemma oneL_off {b : Bits} (hb : ¬ isCode b) : oneL b = 0 := by simp [oneL, hb]

/-! ## Generalised Pauli operators -/

/-- The action of the generalised Pauli `U_{m,z} |b⟩ = (-1)^{z·b} |b + m⟩` on amplitudes. -/
def apU (m z : Bits) (u : Amp) : Amp := fun b => sgn (dot z (b + m)) * u (b + m)

@[simp] lemma apU_zero_zero (u : Amp) : apU 0 0 u = u := by
  funext b; simp [apU]

/-- The fundamental "interference sum". -/
noncomputable def G (M Z : Bits) (u v : Amp) : ℂ :=
  ∑ b : Bits, sgn (dot Z b) * ((starRingEnd ℂ) (u b) * v (b + M))

lemma ipf_apU (m z m' z' : Bits) (u v : Amp) :
    ipf (apU m z u) (apU m' z' v) = sgn (dot z' (m + m')) * G (m + m') (z + z') u v := by
  unfold ipf apU G
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight m)]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Equiv.coe_addRight]
  rw [bits_add_add_cancel b m, add_assoc b m m']
  simp only [map_mul, conj_sgn, dot_add_left, dot_add_right, sgn_add]
  ring

/-! ### The two structural facts -/

lemma isCode_add {b M : Bits} (hb : isCode b) (h : isCode (b + M)) : isCode M := by
  intro r s
  have h1 := hb r s
  have h2 := h r s
  simp only [Pi.add_apply, h1] at h2
  exact add_left_cancel h2

lemma G_eq_zero_of_not_isCode (M Z : Bits) (u v : Amp)
    (hu : ∀ b, ¬ isCode b → u b = 0) (hv : ∀ b, ¬ isCode b → v b = 0)
    (hM : ¬ isCode M) : G M Z u v = 0 := by
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : isCode b
  · rw [hv (b + M) (fun h => hM (isCode_add hb h))]
    ring
  · rw [hu b hb]
    simp

lemma isCode_eq_zero_of_supp (M : Bits) (q q' : Site)
    (h : ∀ p, M p ≠ 0 → p = q ∨ p = q') (hM : isCode M) : M = 0 := by
  funext p
  simp only [Pi.zero_apply]
  by_contra hne
  obtain ⟨r, s⟩ := p
  have hb : M (r, 0) ≠ 0 := by rw [← hM r s]; exact hne
  have h0 : M (r, 0) ≠ 0 := hb
  have h1 : M (r, 1) ≠ 0 := by rw [hM r 1]; exact hb
  have h2 : M (r, 2) ≠ 0 := by rw [hM r 2]; exact hb
  have e0 := h (r, 0) h0
  have e1 := h (r, 1) h1
  have e2 := h (r, 2) h2
  have key : ∀ (s1 s2 : Fin 3) (x : Site), ((r, s1) : Site) = x → ((r, s2) : Site) = x → s1 = s2 :=
    fun s1 s2 x k1 k2 => congrArg Prod.snd (k1.trans k2.symm)
  clear h hne hb h0 h1 h2 hM
  rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  · exact absurd (key 0 1 q e0 e1) (by decide)
  · exact absurd (key 0 1 q e0 e1) (by decide)
  · exact absurd (key 0 2 q e0 e2) (by decide)
  · exact absurd (key 1 2 q' e1 e2) (by decide)
  · exact absurd (key 1 2 q e1 e2) (by decide)
  · exact absurd (key 0 2 q' e0 e2) (by decide)
  · exact absurd (key 0 1 q' e0 e1) (by decide)
  · exact absurd (key 0 1 q' e0 e1) (by decide)

/-! ### The diagonal case `M = 0` -/

lemma G_diag (Z : Bits) : G 0 Z zeroL zeroL = G 0 Z oneL oneL := by
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : isCode b <;>
    simp [zeroL, oneL, hb, mul_comm, mul_left_comm, mul_assoc, sgn_mul_self]

lemma char_sum_zero (w : Fin 3 → ZMod 2) (r0 : Fin 3) (hw : w r0 = 1) :
    ∑ c : Fin 3 → ZMod 2, sgn (∑ r : Fin 3, w r * c r) = 0 := by
  set d : Fin 3 → ZMod 2 := fun r => if r = r0 then 1 else 0 with hd
  set S : ℂ := ∑ c : Fin 3 → ZMod 2, sgn (∑ r : Fin 3, w r * c r) with hS
  have key : S = -S := by
    calc S = ∑ c : Fin 3 → ZMod 2, sgn (∑ r : Fin 3, w r * ((Equiv.addRight d) c) r) := by
            rw [hS, Equiv.sum_comp (Equiv.addRight d)
              (fun c => sgn (∑ r : Fin 3, w r * c r))]
      _ = -S := by
            rw [hS, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun c _ => ?_
            have hsum : ∑ r : Fin 3, w r * ((Equiv.addRight d) c) r
                = (∑ r : Fin 3, w r * c r) + 1 := by
              simp only [Equiv.coe_addRight, Pi.add_apply, mul_add]
              rw [Finset.sum_add_distrib]
              congr 1
              rw [hd]
              simp [Finset.sum_ite_eq' Finset.univ r0, hw]
            rw [hsum, sgn_add, sgn_one]
            ring
  have : (2 : ℂ) * S = 0 := by rw [two_mul]; nth_rewrite 2 [key]; ring
  simpa using this

lemma exists_free_block (q q' : Site) : ∃ r0 : Fin 3, r0 ≠ q.1 ∧ r0 ≠ q'.1 := by
  revert q q'
  decide

lemma dot_rep (Z : Bits) (c : Fin 3 → ZMod 2) :
    dot Z (rep c) = ∑ r : Fin 3, (∑ s : Fin 3, Z (r, s)) * c r := by
  rw [dot, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul]
  rfl

lemma lw_rep (c : Fin 3 → ZMod 2) : lw (rep c) = ∑ r : Fin 3, c r := rfl

/-- The key vanishing: an odd-parity phase pattern supported on at most two qubits
cannot connect `|0_L⟩` to `|1_L⟩`. -/
lemma code_char_sum (Z : Bits) (r0 : Fin 3) (hZ : ∀ s : Fin 3, Z (r0, s) = 0) :
    ∑ c : Fin 3 → ZMod 2, sgn (dot Z (rep c) + lw (rep c)) = 0 := by
  have hrw : ∀ c : Fin 3 → ZMod 2, dot Z (rep c) + lw (rep c)
      = ∑ r : Fin 3, ((∑ s : Fin 3, Z (r, s)) + 1) * c r := by
    intro c
    rw [dot_rep, lw_rep, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  simp only [hrw]
  refine char_sum_zero _ r0 ?_
  simp [hZ]

lemma G_zeroL_oneL_formula (Z : Bits) :
    G 0 Z zeroL oneL
      = kappa * kappa * ∑ c : Fin 3 → ZMod 2, sgn (dot Z (rep c) + lw (rep c)) := by
  rw [G]
  rw [sum_over_code _ (fun b hb => by simp [zeroL_off hb])]
  have : ∀ c : Fin 3 → ZMod 2,
      sgn (dot Z (rep c)) * ((starRingEnd ℂ) (zeroL (rep c)) * oneL (rep c + 0))
        = kappa * kappa * sgn (dot Z (rep c) + lw (rep c)) := by
    intro c
    simp only [add_zero, zeroL, oneL, if_pos (isCode_rep c), conj_kappa, sgn_add]
    ring
  simp only [this, ← Finset.mul_sum]

lemma G_offdiag_zeroL_oneL (Z : Bits) (r0 : Fin 3) (hZ : ∀ s : Fin 3, Z (r0, s) = 0) :
    G 0 Z zeroL oneL = 0 := by
  rw [G_zeroL_oneL_formula, code_char_sum Z r0 hZ, mul_zero]

lemma G_offdiag_oneL_zeroL (Z : Bits) (r0 : Fin 3) (hZ : ∀ s : Fin 3, Z (r0, s) = 0) :
    G 0 Z oneL zeroL = 0 := by
  rw [G]
  rw [sum_over_code _ (fun b hb => by simp [oneL_off hb])]
  have : ∀ c : Fin 3 → ZMod 2,
      sgn (dot Z (rep c)) * ((starRingEnd ℂ) (oneL (rep c)) * zeroL (rep c + 0))
        = kappa * kappa * sgn (dot Z (rep c) + lw (rep c)) := by
    intro c
    simp only [add_zero, zeroL, oneL, if_pos (isCode_rep c), map_mul, conj_kappa, conj_sgn,
      sgn_add]
    ring
  simp only [this, ← Finset.mul_sum, code_char_sum Z r0 hZ, mul_zero]

/-! ### Knill–Laflamme for a pair of generalised Paulis -/

lemma KL_pair (q q' : Site) (m z m' z' : Bits)
    (hm : ∀ p, m p ≠ 0 → p = q) (hz : ∀ p, z p ≠ 0 → p = q)
    (hm' : ∀ p, m' p ≠ 0 → p = q') (hz' : ∀ p, z' p ≠ 0 → p = q') :
    ipf (apU m z zeroL) (apU m' z' oneL) = 0 ∧
    ipf (apU m z oneL) (apU m' z' zeroL) = 0 ∧
    ipf (apU m z zeroL) (apU m' z' zeroL) = ipf (apU m z oneL) (apU m' z' oneL) := by
  have hsupp : ∀ (x y : Bits), (∀ p, x p ≠ 0 → p = q) → (∀ p, y p ≠ 0 → p = q') →
      ∀ p, (x + y) p ≠ 0 → p = q ∨ p = q' := by
    intro x y hx hy p hp
    simp only [Pi.add_apply] at hp
    by_cases h1 : x p = 0
    · right
      refine hy p ?_
      intro h2
      exact hp (by rw [h1, h2, add_zero])
    · exact Or.inl (hx p h1)
  rw [ipf_apU, ipf_apU, ipf_apU, ipf_apU]
  by_cases hM : isCode (m + m')
  · have hM0 : m + m' = 0 :=
      isCode_eq_zero_of_supp _ q q' (hsupp m m' hm hm') hM
    obtain ⟨r0, hr0, hr0'⟩ := exists_free_block q q'
    have hZ : ∀ s : Fin 3, (z + z') (r0, s) = 0 := by
      intro s
      simp only [Pi.add_apply]
      have h1 : z (r0, s) = 0 := by
        by_contra h
        exact hr0 (congrArg Prod.fst (hz _ h))
      have h2 : z' (r0, s) = 0 := by
        by_contra h
        exact hr0' (congrArg Prod.fst (hz' _ h))
      rw [h1, h2, add_zero]
    rw [hM0]
    refine ⟨?_, ?_, ?_⟩
    · rw [G_offdiag_zeroL_oneL _ r0 hZ, mul_zero]
    · rw [G_offdiag_oneL_zeroL _ r0 hZ, mul_zero]
    · rw [G_diag]
  · have h0 : ∀ u v : Amp, (∀ b, ¬ isCode b → u b = 0) → (∀ b, ¬ isCode b → v b = 0) →
        G (m + m') (z + z') u v = 0 :=
      fun u v hu hv => G_eq_zero_of_not_isCode _ _ u v hu hv hM
    rw [h0 zeroL oneL (fun _ => zeroL_off) (fun _ => oneL_off),
      h0 oneL zeroL (fun _ => oneL_off) (fun _ => zeroL_off),
      h0 zeroL zeroL (fun _ => zeroL_off) (fun _ => zeroL_off),
      h0 oneL oneL (fun _ => oneL_off) (fun _ => oneL_off)]
    simp

/-! ## Linearity of the inner product -/

lemma ipf_sum_left {ι : Type} (s : Finset ι) (f : ι → Amp) (v : Amp) :
    ipf (∑ i ∈ s, f i) v = ∑ i ∈ s, ipf (f i) v := by
  simp only [ipf, Finset.sum_apply, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

lemma ipf_sum_right {ι : Type} (s : Finset ι) (u : Amp) (g : ι → Amp) :
    ipf u (∑ i ∈ s, g i) = ∑ i ∈ s, ipf u (g i) := by
  simp only [ipf, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma ipf_smul_left (a : ℂ) (u v : Amp) : ipf (a • u) v = (starRingEnd ℂ) a * ipf u v := by
  simp only [ipf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

lemma ipf_smul_right (a : ℂ) (u v : Amp) : ipf u (a • v) = a * ipf u v := by
  simp only [ipf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-! ## Pauli matrices on the 9-qubit register -/

/-- The generalised Pauli matrix `U_{m,z} : |b⟩ ↦ (-1)^{z·b} |b + m⟩`. -/
def Umat (m z : Bits) : Matrix Bits Bits ℂ :=
  Matrix.of fun b b' => if b = b' + m then sgn (dot z b') else 0

lemma Umat_mulVec (m z : Bits) (u : Amp) : (Umat m z).mulVec u = apU m z u := by
  funext b
  show ∑ b' : Bits, Umat m z b b' * u b' = apU m z u b
  rw [Finset.sum_eq_single (b + m)]
  · simp [Umat, apU, bits_add_add_cancel]
  · intro b' _ hb'
    have : ¬ (b = b' + m) := by
      intro h
      exact hb' (by rw [h, bits_add_add_cancel])
    simp [Umat, this]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Pauli `X` on qubit `q`. -/
def pauliX (q : Site) : Matrix Bits Bits ℂ :=
  Matrix.of fun b b' => if b = b' + e q then 1 else 0

/-- Pauli `Z` on qubit `q`. -/
def pauliZ (q : Site) : Matrix Bits Bits ℂ :=
  Matrix.of fun b b' => if b = b' then sgn (b' q) else 0

/-- Pauli `Y` on qubit `q`. -/
def pauliY (q : Site) : Matrix Bits Bits ℂ :=
  Matrix.of fun b b' => if b = b' + e q then Complex.I * sgn (b' q) else 0

lemma pauliX_eq (q : Site) : pauliX q = Umat (e q) 0 := by
  funext b b'; simp [pauliX, Umat]

lemma pauliZ_eq (q : Site) : pauliZ q = Umat 0 (e q) := by
  funext b b'; simp [pauliZ, Umat]

lemma pauliY_eq (q : Site) : pauliY q = Complex.I • Umat (e q) (e q) := by
  funext b b'
  by_cases h : b = b' + e q <;> simp [pauliY, Umat, h]

lemma one_eq_Umat : (1 : Matrix Bits Bits ℂ) = Umat 0 0 := by
  funext b b'
  by_cases h : b = b' <;> simp [Matrix.one_apply, Umat, h]

/-- The coefficient vector of a single-qubit error, written in the generalised-Pauli basis. -/
def coefV (a b c d : ℂ) : Fin 4 → ℂ := ![a, b, c * Complex.I, d]

/-- The bit-flip parts of the four generalised Paulis at qubit `q`. -/
def mV (q : Site) : Fin 4 → Bits := ![0, e q, e q, 0]

/-- The phase parts of the four generalised Paulis at qubit `q`. -/
def zV (q : Site) : Fin 4 → Bits := ![0, 0, e q, e q]

lemma mV_supp (q : Site) (k : Fin 4) : ∀ p, mV q k p ≠ 0 → p = q := by
  fin_cases k <;> intro p hp <;> first
    | exact absurd rfl hp
    | exact e_supp hp

lemma zV_supp (q : Site) (k : Fin 4) : ∀ p, zV q k p ≠ 0 → p = q := by
  fin_cases k <;> intro p hp <;> first
    | exact absurd rfl hp
    | exact e_supp hp

lemma mulVec_expand (q : Site) (a b c d : ℂ) (u : Amp) :
    (a • (1 : Matrix Bits Bits ℂ) + b • pauliX q + c • pauliY q + d • pauliZ q).mulVec u
      = ∑ k : Fin 4, coefV a b c d k • apU (mV q k) (zV q k) u := by
  rw [Fin.sum_univ_four]
  simp only [coefV, mV, zV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, pauliX_eq, pauliY_eq, pauliZ_eq,
    one_eq_Umat, Umat_mulVec, smul_smul]

/-! ## Knill–Laflamme for arbitrary single-qubit errors -/

lemma ipf_expand (α β : Fin 4 → ℂ) (f g : Fin 4 → Amp) :
    ipf (∑ k : Fin 4, α k • f k) (∑ l : Fin 4, β l • g l)
      = ∑ k : Fin 4, ∑ l : Fin 4, (starRingEnd ℂ) (α k) * β l * ipf (f k) (g l) := by
  rw [ipf_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ipf_smul_left, ipf_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ipf_smul_right]
  ring

/-- An operator on the 9-qubit register is an *arbitrary single-qubit error* if it acts as an
arbitrary `2 × 2` matrix `a·I + b·X + c·Y + d·Z` on one qubit and as the identity elsewhere. -/
def SingleQubitError (E : Matrix Bits Bits ℂ) : Prop :=
  ∃ (q : Site) (a b c d : ℂ), E = a • 1 + b • pauliX q + c • pauliY q + d • pauliZ q

lemma sum_swap3 (T : Bits → Bits → Bits → ℂ) :
    (∑ b : Bits, ∑ d : Bits, ∑ c : Bits, T b d c)
      = ∑ c : Bits, ∑ b : Bits, ∑ d : Bits, T b d c := by
  rw [show (∑ b : Bits, ∑ d : Bits, ∑ c : Bits, T b d c)
        = ∑ b : Bits, ∑ c : Bits, ∑ d : Bits, T b d c from
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  exact Finset.sum_comm

lemma ipf_adjoint (E F : Matrix Bits Bits ℂ) (u v : Amp) :
    ipf u ((Eᴴ * F).mulVec v) = ipf (E.mulVec u) (F.mulVec v) := by
  have hL : ipf u ((Eᴴ * F).mulVec v)
      = ∑ b : Bits, ∑ d : Bits, ∑ c : Bits,
          star (u b) * star (E c b) * F c d * v d := by
    simp only [ipf, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
      starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
      Finset.sum_congr rfl fun c _ => by ring
  have hR : ipf (E.mulVec u) (F.mulVec v)
      = ∑ c : Bits, ∑ d : Bits, ∑ b : Bits,
          star (u b) * star (E c b) * F c d * v d := by
    simp only [ipf, Matrix.mulVec, dotProduct, starRingEnd_apply, star_sum, star_mul',
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
      Finset.sum_congr rfl fun b _ => by ring
  rw [hL, hR, sum_swap3]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **The Shor code corrects an arbitrary single-qubit error.**

This is the Knill–Laflamme error-correction condition for the nine-qubit Shor code: for any
two errors `E`, `F` each acting arbitrarily on a single (possibly different) qubit, the matrix
of `Eᴴ * F` on the two-dimensional code space spanned by `|0_L⟩`, `|1_L⟩` is a scalar
multiple of the identity.  Equivalently, no such error leaks any information about the encoded
logical state, and a recovery operation exists. -/
theorem shor_code_corrects (E F : Matrix Bits Bits ℂ)
    (hE : SingleQubitError E) (hF : SingleQubitError F) :
    ∃ lam : ℂ,
      ipf zeroL ((Eᴴ * F).mulVec zeroL) = lam ∧
      ipf oneL ((Eᴴ * F).mulVec oneL) = lam ∧
      ipf zeroL ((Eᴴ * F).mulVec oneL) = 0 ∧
      ipf oneL ((Eᴴ * F).mulVec zeroL) = 0 := by
  obtain ⟨q, a, b, c, d, rfl⟩ := hE
  obtain ⟨q', a', b', c', d', rfl⟩ := hF
  refine ⟨ipf zeroL (((a • 1 + b • pauliX q + c • pauliY q + d • pauliZ q)ᴴ *
      (a' • 1 + b' • pauliX q' + c' • pauliY q' + d' • pauliZ q')).mulVec zeroL), rfl, ?_, ?_, ?_⟩
  · rw [ipf_adjoint, ipf_adjoint, mulVec_expand, mulVec_expand, mulVec_expand, mulVec_expand,
      ipf_expand, ipf_expand]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [(KL_pair q q' (mV q k) (zV q k) (mV q' l) (zV q' l) (mV_supp q k) (zV_supp q k)
      (mV_supp q' l) (zV_supp q' l)).2.2]
  · rw [ipf_adjoint, mulVec_expand, mulVec_expand, ipf_expand]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    rw [(KL_pair q q' (mV q k) (zV q k) (mV q' l) (zV q' l) (mV_supp q k) (zV_supp q k)
      (mV_supp q' l) (zV_supp q' l)).1, mul_zero]
  · rw [ipf_adjoint, mulVec_expand, mulVec_expand, ipf_expand]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    rw [(KL_pair q q' (mV q k) (zV q k) (mV q' l) (zV q' l) (mV_supp q k) (zV_supp q k)
      (mV_supp q' l) (zV_supp q' l)).2.1, mul_zero]

/-! ## The logical states really are an orthonormal pair -/

lemma ipf_eq_G (u v : Amp) : ipf u v = G 0 0 u v := by
  simp [ipf, G]

theorem shor_logical_orthonormal :
    ipf zeroL zeroL = 1 ∧ ipf oneL oneL = 1 ∧ ipf zeroL oneL = 0 ∧ ipf oneL zeroL = 0 := by
  have hz : ∀ s : Fin 3, (0 : Bits) (0, s) = 0 := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ipf, sum_over_code _ (fun b hb => by simp [zeroL_off hb])]
    simp only [zeroL, if_pos (isCode_rep _), conj_kappa]
    rw [Finset.sum_const, kappa_sq]
    norm_num
  · rw [ipf, sum_over_code _ (fun b hb => by simp [oneL_off hb])]
    have : ∀ c : Fin 3 → ZMod 2,
        (starRingEnd ℂ) (oneL (rep c)) * oneL (rep c) = kappa * kappa := by
      intro c
      simp only [oneL, if_pos (isCode_rep c), map_mul, conj_kappa, conj_sgn]
      rw [show sgn (lw (rep c)) * kappa * (sgn (lw (rep c)) * kappa)
        = sgn (lw (rep c)) * sgn (lw (rep c)) * (kappa * kappa) by ring, sgn_mul_self, one_mul]
    simp only [this]
    rw [Finset.sum_const, kappa_sq]
    norm_num
  · rw [ipf_eq_G]
    exact G_offdiag_zeroL_oneL 0 0 hz
  · rw [ipf_eq_G]
    exact G_offdiag_oneL_zeroL 0 0 hz

/-! ## Sharpness: the hypothesis on the weight of the error cannot be dropped

The operator `Z^{⊗ 9}` (a Pauli `Z` on every one of the nine qubits) is a *logical* bit flip:
it maps `|1_L⟩` to `|0_L⟩`.  Hence the Knill–Laflamme off-diagonal condition genuinely fails
for it, which shows that `shor_code_corrects` is not vacuously true and that the restriction
to errors supported on a single qubit is essential. -/

/-- The all-ones bit string; `Umat 0 allOnes` is `Z` applied to every qubit. -/
def allOnes : Bits := fun _ => 1

lemma ipf_Umat_zero (Z : Bits) (u v : Amp) :
    ipf u ((Umat 0 Z).mulVec v) = G 0 Z u v := by
  rw [Umat_mulVec, ipf, G]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [apU, add_zero]
  ring

lemma dot_allOnes_rep (c : Fin 3 → ZMod 2) : dot allOnes (rep c) = lw (rep c) := by
  rw [dot_rep, lw_rep]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h1 : (∑ _s : Fin 3, allOnes ((r, _s) : Site)) = 1 := by
    simp only [allOnes, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    decide
  rw [h1, one_mul]

/-- `Z^{⊗ 9}` is a logical bit flip on the Shor code: `⟨0_L| Z^{⊗ 9} |1_L⟩ = 1`. -/
theorem shor_all_Z_is_logical_flip : ipf zeroL ((Umat 0 allOnes).mulVec oneL) = 1 := by
  rw [ipf_Umat_zero, G_zeroL_oneL_formula]
  have h1 : ∀ c : Fin 3 → ZMod 2, sgn (dot allOnes (rep c) + lw (rep c)) = 1 := by
    intro c
    rw [dot_allOnes_rep, CharTwo.add_self_eq_zero, sgn_zero]
  have hcard : Fintype.card (Fin 3 → ZMod 2) = 8 := by decide
  simp only [h1, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  rw [kappa_sq]
  norm_num

end QI

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

