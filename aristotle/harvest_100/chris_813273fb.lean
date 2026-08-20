import Mathlib
/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands in a
file, and `/-! ... -/` is a module doc-comment *command*, not a comment token.  The
required header block is therefore placed immediately after the single `import Mathlib`
line, which is the closest legal position to the top of the file.
-/

namespace QI

open Finset

noncomputable section

/-! ## The 9-qubit state space -/

/-- Qubit labels: three blocks of three qubits. -/
abbrev Qb := Fin 3 × Fin 3

/-- Computational basis labels for 9 qubits. -/
abbrev Cfg := Qb → Bool

/-- The state space of 9 qubits, `ℂ^(2^9)`. -/
abbrev H := Cfg → ℂ

/-- Hermitian inner product, conjugate linear in the first argument. -/
def ip (x y : H) : ℂ := ∑ v : Cfg, (starRingEnd ℂ) (x v) * y v

lemma ip_add_right (x y z : H) : ip x (y + z) = ip x y + ip x z := by
  simp [ip, mul_add, Finset.sum_add_distrib]

lemma ip_add_left (x y z : H) : ip (x + y) z = ip x z + ip y z := by
  simp [ip, add_mul, Finset.sum_add_distrib]

lemma ip_smul_right (c : ℂ) (x y : H) : ip x (c • y) = c * ip x y := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

lemma ip_smul_left (c : ℂ) (x y : H) : ip (c • x) y = (starRingEnd ℂ) c * ip x y := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun v _ => by ring

lemma ip_sub_right (x y z : H) : ip x (y - z) = ip x y - ip x z := by
  simp [ip, mul_sub, Finset.sum_sub_distrib]

lemma ip_sub_left (x y z : H) : ip (x - y) z = ip x z - ip y z := by
  simp [ip, sub_mul, Finset.sum_sub_distrib]

lemma ip_sum_right {ι : Type*} (s : Finset ι) (x : H) (f : ι → H) :
    ip x (∑ i ∈ s, f i) = ∑ i ∈ s, ip x (f i) := by
  simp only [ip, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma ip_sum_left {ι : Type*} (s : Finset ι) (x : H) (f : ι → H) :
    ip (∑ i ∈ s, f i) x = ∑ i ∈ s, ip (f i) x := by
  simp only [ip, Finset.sum_apply, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

lemma ip_conj (x y : H) : (starRingEnd ℂ) (ip x y) = ip y x := by
  simp only [ip, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun v _ => by ring

/-! ## Signs and Pauli operators -/

/-- `(-1)^b`. -/
def sg (b : Bool) : ℂ := if b then -1 else 1

@[simp] lemma sg_false : sg false = 1 := rfl
@[simp] lemma sg_true : sg true = -1 := rfl

lemma sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

/-- Bitwise xor of configurations. -/
def xr (v u : Cfg) : Cfg := fun q => xor (v q) (u q)

/-- The zero configuration. -/
def zc : Cfg := fun _ => false

/-- The configuration with a single `true` at `i`. -/
def uc (i : Qb) : Cfg := fun q => decide (q = i)

@[simp] lemma xr_zc (v : Cfg) : xr v zc = v := by funext q; simp [xr, zc]

@[simp] lemma xr_self (v : Cfg) : xr v v = zc := by funext q; simp [xr, zc]

lemma xr_xr (v u : Cfg) : xr (xr v u) u = v := by
  funext q; simp [xr]

lemma xr_comm (v u : Cfg) : xr v u = xr u v := by funext q; simp [xr, Bool.xor_comm]

@[simp] lemma uc_apply_self (i : Qb) : uc i i = true := by simp [uc]

/-- The sign `(-1)^(w ⬝ v)` produced by a product of `Z`s. -/
def zph (w v : Cfg) : ℂ := ∏ q : Qb, sg (w q && v q)

@[simp] lemma zph_zc_left (v : Cfg) : zph zc v = 1 := by simp [zph, zc]

@[simp] lemma zph_zc_right (w : Cfg) : zph w zc = 1 := by simp [zph, zc]

lemma zph_xor_right (w t s : Cfg) : zph w (xr t s) = zph w t * zph w s := by
  simp only [zph, xr, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  cases w q <;> cases t q <;> cases s q <;> simp [sg]

lemma zph_xor_left (w1 w2 v : Cfg) : zph (xr w1 w2) v = zph w1 v * zph w2 v := by
  simp only [zph, xr, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  cases w1 q <;> cases w2 q <;> cases v q <;> simp [sg]

lemma zph_uc (i : Qb) (v : Cfg) : zph (uc i) v = sg (v i) := by
  simp only [zph, uc]
  rw [Finset.prod_eq_single i]
  · simp
  · intro q _ hq; simp [hq]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma zph_mul_self (w t : Cfg) : zph w t * zph w t = 1 := by
  simp only [zph, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun q _ => sg_mul_self _

lemma zph_shift (w1 w2 t U : Cfg) :
    zph w1 t * zph w2 (xr t U) = zph w1 U * zph (xr w1 w2) (xr t U) := by
  rw [zph_xor_right, zph_xor_left, zph_xor_right, zph_xor_right]
  calc zph w1 t * (zph w2 t * zph w2 U)
      = 1 * (zph w1 t * (zph w2 t * zph w2 U)) := by ring
    _ = (zph w1 U * zph w1 U) * (zph w1 t * (zph w2 t * zph w2 U)) := by rw [zph_mul_self]
    _ = _ := by ring

/-- The Pauli operator `X^u Z^w`. -/
def Pauli (u w : Cfg) : H →ₗ[ℂ] H where
  toFun ψ := fun v => zph w (xr v u) * ψ (xr v u)
  map_add' := by intro x y; funext v; simp [mul_add]
  map_smul' := by intro c x; funext v; simp [smul_eq_mul]; ring

lemma Pauli_apply (u w : Cfg) (ψ : H) (v : Cfg) :
    Pauli u w ψ v = zph w (xr v u) * ψ (xr v u) := rfl

@[simp] lemma Pauli_zc_zc (ψ : H) : Pauli zc zc ψ = ψ := by
  funext v; simp [Pauli_apply]

/-- Composition rule turning an inner product of two Pauli-corrupted states into a single
Pauli inner product. -/
lemma ip_Pauli_Pauli (u1 w1 u2 w2 : Cfg) (x y : H) :
    ip (Pauli u1 w1 x) (Pauli u2 w2 y)
      = zph w1 (xr u1 u2) * ip x (Pauli (xr u1 u2) (xr w1 w2) y) := by
  have hz : ∀ t : Cfg, (starRingEnd ℂ) (zph w1 t) = zph w1 t := by
    intro t
    simp only [zph, map_prod]
    exact Finset.prod_congr rfl fun q _ => by cases (w1 q && t q) <;> simp [sg]
  simp only [ip, Pauli_apply, Finset.mul_sum]
  -- reindex `v ↦ xr v u1`
  rw [← Equiv.sum_comp (Equiv.mk (fun v => xr v u1) (fun v => xr v u1)
      (fun v => by simp [xr_xr]) (fun v => by simp [xr_xr]))]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Equiv.coe_fn_mk, xr_xr, map_mul, hz]
  have h1 : xr (xr t u1) u2 = xr t (xr u1 u2) := by
    funext q; simp [xr]
  rw [h1]
  have h2 : zph w2 (xr t (xr u1 u2)) = zph w2 t * zph w2 (xr u1 u2) := zph_xor_right _ _ _
  linear_combination ((starRingEnd ℂ) (x t) * y (xr t (xr u1 u2))) * zph_shift w1 w2 t (xr u1 u2)

/-! ## Block-constant configurations -/

/-- A configuration is *block constant* if it is constant on each block of three qubits. -/
def blkish (v : Cfg) : Prop := ∀ b k k' : Fin 3, v (b, k) = v (b, k')

instance (v : Cfg) : Decidable (blkish v) := by unfold blkish; infer_instance

/-- The block-constant configuration determined by three bits. -/
def blk (c : Fin 3 → Bool) : Cfg := fun q => c q.1

/-- The bits of a block-constant configuration. -/
def bits (v : Cfg) : Fin 3 → Bool := fun b => v (b, 0)

lemma blk_blkish (c : Fin 3 → Bool) : blkish (blk c) := fun _ _ _ => rfl

@[simp] lemma bits_blk (c : Fin 3 → Bool) : bits (blk c) = c := rfl

lemma blk_bits {v : Cfg} (h : blkish v) : blk (bits v) = v := by
  funext q
  obtain ⟨b, k⟩ := q
  exact (h b 0 k)

lemma blk_inj {c c' : Fin 3 → Bool} (h : blk c = blk c') : c = c' := by
  funext b; exact congrFun h (b, 0)

lemma blkish_zc : blkish zc := fun _ _ _ => rfl

lemma not_blkish_xr {v u : Cfg} (hv : blkish v) (hu : ¬ blkish u) : ¬ blkish (xr v u) := by
  intro h
  apply hu
  intro b k k'
  have h1 : xor (v (b,k)) (u (b,k)) = xor (v (b,k')) (u (b,k')) := h b k k'
  have h2 : v (b,k) = v (b,k') := hv b k k'
  revert h1 h2
  cases v (b,k) <;> cases v (b,k') <;> cases u (b,k) <;> cases u (b,k') <;> simp

lemma sum_blkish (f : Cfg → ℂ) :
    ∑ v : Cfg, (if blkish v then f v else 0) = ∑ c : Fin 3 → Bool, f (blk c) := by
  rw [← Finset.sum_filter]
  have himg : Finset.univ.filter blkish = Finset.image blk Finset.univ := by
    ext v
    constructor
    · intro h
      exact Finset.mem_image.2 ⟨bits v, Finset.mem_univ _, blk_bits (Finset.mem_filter.1 h).2⟩
    · intro h
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, blk_blkish c⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => blk_inj h)]

/-! ## The Shor code -/

/-- The sign `(-1)^(number of blocks set)`. -/
def sgnc (c : Fin 3 → Bool) : ℂ := ∏ b : Fin 3, sg (c b)

/-- Normalisation `1/(2√2)`. -/
def nrm : ℂ := ((Real.sqrt 8 : ℝ) : ℂ)⁻¹

lemma nrm_sq : nrm * nrm = 1 / 8 := by
  have h8 : ((Real.sqrt 8 : ℝ) : ℂ) * ((Real.sqrt 8 : ℝ) : ℂ) = 8 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  show ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ = 1 / 8
  rw [← mul_inv, h8]
  norm_num

lemma nrm_conj : (starRingEnd ℂ) nrm = nrm := by
  simp only [nrm, map_inv₀, Complex.conj_ofReal]

/-- The two logical basis states of the Shor code:
`L false = (|000⟩+|111⟩)^{⊗3}/(2√2)`, `L true = (|000⟩-|111⟩)^{⊗3}/(2√2)`. -/
def L (a : Bool) : H :=
  fun v => if blkish v then nrm * (if a then sgnc (bits v) else 1) else 0

lemma sgnc_conj (c : Fin 3 → Bool) : (starRingEnd ℂ) (sgnc c) = sgnc c := by
  simp only [sgnc, map_prod]
  exact Finset.prod_congr rfl fun b _ => by cases c b <;> simp [sg]

lemma L_conj (a : Bool) (v : Cfg) : (starRingEnd ℂ) (L a v) = L a v := by
  simp only [L]
  split
  · rw [map_mul, nrm_conj]
    congr 1
    cases a
    · simp
    · simpa using sgnc_conj (bits v)
  · simp

lemma L_not_blkish {a : Bool} {v : Cfg} (h : ¬ blkish v) : L a v = 0 := by simp [L, h]

lemma L_blk (a : Bool) (c : Fin 3 → Bool) :
    L a (blk c) = nrm * (if a then sgnc c else 1) := by
  simp [L, blk_blkish c]

lemma ip_L (a : Bool) (y : H) : ip (L a) y = ∑ c : Fin 3 → Bool, L a (blk c) * y (blk c) := by
  rw [ip]
  have h : ∀ v : Cfg, (starRingEnd ℂ) (L a v) * y v = if blkish v then L a v * y v else 0 := by
    intro v
    by_cases hv : blkish v
    · simp [hv, L_conj]
    · simp [hv, L_not_blkish hv]
  simp_rw [h]
  exact sum_blkish _

/-! ## Block parities -/

/-- Parity of the `Z`-support in block `b`. -/
def mpar (w : Cfg) (b : Fin 3) : Bool := xor (xor (w (b, 0)) (w (b, 1))) (w (b, 2))

/-- The sign contributed by block `b`. -/
def mu (w : Cfg) (b : Fin 3) : ℂ := ∏ k : Fin 3, sg (w (b, k))

lemma mu_eq (w : Cfg) (b : Fin 3) : mu w b = sg (mpar w b) := by
  simp only [mu, mpar, Fin.prod_univ_three]
  cases w (b,0) <;> cases w (b,1) <;> cases w (b,2) <;> norm_num [sg]

lemma zph_blk (w : Cfg) (c : Fin 3 → Bool) :
    zph w (blk c) = ∏ b : Fin 3, (if c b then mu w b else 1) := by
  simp only [zph, Fintype.prod_prod_type, blk, mu]
  refine Finset.prod_congr rfl fun b _ => ?_
  by_cases h : c b
  · simp [h]
  · simp [h]

/-- The key inner product computation for the Shor code. -/
lemma ip_L_Pauli_zc (a b : Bool) (w : Cfg) :
    ip (L a) (Pauli zc w (L b))
      = (nrm * nrm) * ∏ β : Fin 3, (1 + (if a = b then (1 : ℂ) else -1) * mu w β) := by
  rw [ip_L]
  have step : ∀ c : Fin 3 → Bool,
      L a (blk c) * (Pauli zc w (L b)) (blk c)
        = (nrm * nrm) * ∏ β : Fin 3,
            ((if a = b then (1 : ℂ) else sg (c β)) * (if c β then mu w β else 1)) := by
    intro c
    rw [Pauli_apply, xr_zc, L_blk, L_blk, zph_blk]
    rw [Finset.prod_mul_distrib]
    have hsg : (if a then sgnc c else (1:ℂ)) * (if b then sgnc c else (1:ℂ))
        = ∏ β : Fin 3, (if a = b then (1:ℂ) else sg (c β)) := by
      have hsq : sgnc c * sgnc c = 1 := by
        rw [sgnc, ← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun β _ => sg_mul_self _
      cases a <;> cases b
      · simp
      · simp [sgnc]
      · simp [sgnc]
      · simpa using hsq
    calc nrm * (if a then sgnc c else 1) *
            ((∏ β : Fin 3, (if c β then mu w β else 1)) * (nrm * (if b then sgnc c else 1)))
        = (nrm * nrm) * ((if a then sgnc c else (1:ℂ)) * (if b then sgnc c else (1:ℂ)))
            * ∏ β : Fin 3, (if c β then mu w β else 1) := by ring
      _ = (nrm * nrm) * (∏ β : Fin 3, (if a = b then (1:ℂ) else sg (c β)))
            * ∏ β : Fin 3, (if c β then mu w β else 1) := by rw [hsg]
      _ = _ := by rw [mul_assoc, ← Finset.prod_mul_distrib]
  simp_rw [step]
  rw [← Finset.mul_sum]
  congr 1
  -- expand the product of sums
  have := Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset Bool))
      (fun (β : Fin 3) (x : Bool) =>
        (if a = b then (1 : ℂ) else sg x) * (if x then mu w β else 1))
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  refine Finset.prod_congr rfl fun β _ => ?_
  rw [Fintype.sum_bool]
  by_cases hab : a = b <;> simp [hab, sg] <;> ring

/-- The main structural fact: an inner product between two Pauli-corrupted logical states. -/
lemma ip_key (a b : Bool) (u w : Cfg)
    (h : ¬ blkish u ∨ (u = zc ∧ ¬ (∀ β : Fin 3, mpar w β = true))) :
    ip (L a) (Pauli u w (L b))
      = if u = zc ∧ (∀ β : Fin 3, mpar w β = false) then (if a = b then 1 else 0) else 0 := by
  rcases h with hu | ⟨hu0, hnall⟩
  · have hne : ¬ (u = zc ∧ (∀ β : Fin 3, mpar w β = false)) := by
      rintro ⟨rfl, -⟩; exact hu blkish_zc
    rw [if_neg hne, ip_L]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Pauli_apply, L_not_blkish (not_blkish_xr (blk_blkish c) hu), mul_zero, mul_zero]
  · subst hu0
    rw [ip_L_Pauli_zc]
    simp only [true_and]
    by_cases hall : ∀ β : Fin 3, mpar w β = false
    · have hmu : ∀ β : Fin 3, mu w β = 1 := fun β => by rw [mu_eq, hall β]; rfl
      simp only [if_pos hall]
      by_cases hab : a = b
      · simp only [if_pos hab]
        have hp : ∀ β ∈ (Finset.univ : Finset (Fin 3)), (1 + (1:ℂ) * mu w β) = 2 := by
          intro β _; rw [hmu β]; norm_num
        rw [Finset.prod_congr rfl hp]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [nrm_sq]; norm_num
      · simp only [if_neg hab]
        rw [Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3)) (by rw [hmu]; norm_num)]
        ring
    · simp only [if_neg hall]
      push_neg at hall
      obtain ⟨β0, hβ0⟩ := hall
      have hβ0' : mu w β0 = -1 := by
        have hb0 : mpar w β0 = true := by simpa using hβ0
        rw [mu_eq, hb0]; rfl
      by_cases hab : a = b
      · simp only [if_pos hab]
        rw [Finset.prod_eq_zero (Finset.mem_univ β0) (by rw [hβ0']; norm_num)]
        ring
      · simp only [if_neg hab]
        push_neg at hnall
        obtain ⟨β1, hβ1⟩ := hnall
        have hβ1' : mu w β1 = 1 := by
          have hb1 : mpar w β1 = false := by simpa using hβ1
          rw [mu_eq, hb1]; rfl
        rw [Finset.prod_eq_zero (Finset.mem_univ β1) (by rw [hβ1']; norm_num)]
        ring

/-! ## Single qubit errors -/

/-- Replace the value at qubit `i`. -/
def setq (v : Cfg) (i : Qb) (b : Bool) : Cfg := fun q => if q = i then b else v q

/-- An arbitrary single-qubit operator `M` acting on qubit `i`. -/
def err (i : Qb) (M : Bool → Bool → ℂ) : H →ₗ[ℂ] H where
  toFun ψ := fun v => ∑ b : Bool, M (v i) b * ψ (setq v i b)
  map_add' := by intro x y; funext v; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x; funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by ring)

/-- Sanity check on the error model: the identity `2 × 2` matrix acts as the identity. -/
lemma err_id (i : Qb) (psi : H) : err i (fun x y => if x = y then 1 else 0) psi = psi := by
  funext v
  have hset : setq v i (v i) = v := by
    funext q; simp only [setq]; split <;> simp_all
  show ∑ b : Bool, (if v i = b then (1:ℂ) else 0) * psi (setq v i b) = psi v
  rw [Finset.sum_eq_single (v i) (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
  simp [hset]

/-! ## The correctable error basis -/

/-- Index set for a maximal set of inequivalent single-qubit Pauli errors:
identity, `X i` and `X i Z i` for each qubit `i`, and one `Z` per block. -/
abbrev J := (Option (Qb × Bool)) ⊕ (Fin 3)

/-- `X`-part of the `j`-th error. -/
def uu : J → Cfg
  | .inl none => zc
  | .inl (some (i, _)) => uc i
  | .inr _ => zc

/-- `Z`-part of the `j`-th error. -/
def ww : J → Cfg
  | .inl none => zc
  | .inl (some (i, y)) => if y then uc i else zc
  | .inr b => uc (b, 0)

/-- The orthonormal family of error-corrupted logical states. -/
def V (m : J × Bool) : H := Pauli (uu m.1) (ww m.1) (L m.2)

/-- Which error class the Pauli `X^p Z^q` on qubit `i` belongs to. -/
def corr (i : Qb) (p q : Bool) : J :=
  if p then .inl (some (i, q)) else if q then .inr i.1 else .inl none

/-- `X^p` at qubit `i`. -/
def pu (i : Qb) (p : Bool) : Cfg := if p then uc i else zc

/-- Coefficient of `X^p Z^q` at qubit `i` in the expansion of the operator `M`. -/
def coef (M : Bool → Bool → ℂ) (p q : Bool) : ℂ :=
  match p, q with
  | false, false => (M false false + M true true) / 2
  | false, true  => (M false false - M true true) / 2
  | true,  false => (M false true + M true false) / 2
  | true,  true  => (M true false - M false true) / 2

/-! ## Orthonormality -/

lemma good_pairs (j k : J) :
    ¬ blkish (xr (uu j) (uu k)) ∨
      (xr (uu j) (uu k) = zc ∧ ¬ (∀ β : Fin 3, mpar (xr (ww j) (ww k)) β = true)) := by
  revert j k; decide

lemma cond_pairs (j k : J) :
    ((xr (uu j) (uu k) = zc ∧ (∀ β : Fin 3, mpar (xr (ww j) (ww k)) β = false)) ↔ j = k) := by
  revert j k; decide

lemma V_orthonormal (m n : J × Bool) : ip (V m) (V n) = if m = n then 1 else 0 := by
  obtain ⟨j, a⟩ := m
  obtain ⟨k, b⟩ := n
  simp only [V]
  rw [ip_Pauli_Pauli, ip_key a b _ _ (good_pairs j k)]
  by_cases hjk : j = k
  · subst hjk
    have h1 : (xr (uu j) (uu j) = zc ∧ (∀ β : Fin 3, mpar (xr (ww j) (ww j)) β = false)) :=
      (cond_pairs j j).2 rfl
    rw [if_pos h1, h1.1, zph_zc_right, one_mul]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Prod.ext_iff]
  · rw [if_neg (fun hc => hjk ((cond_pairs j k).1 hc))]
    simp [hjk, Prod.ext_iff]

/-! ## Expansion of a single-qubit error in the error basis -/

lemma Pauli_pu_L (i : Qb) (p q : Bool) (a : Bool) :
    Pauli (pu i p) (pu i q) (L a) = V (corr i p q, a) := by
  cases p
  · cases q
    · rfl
    · -- degeneracy:  Z_{b,k} and Z_{b,0} agree on the code space
      simp only [pu, corr, V, uu, ww, if_true, if_false, Bool.false_eq_true]
      funext v
      rw [Pauli_apply, Pauli_apply, xr_zc, zph_uc, zph_uc]
      by_cases hv : blkish v
      · congr 2
        obtain ⟨b, k⟩ := i
        exact hv b k 0
      · rw [L_not_blkish hv]; ring
  · cases q <;> rfl

lemma err_L (i : Qb) (M : Bool → Bool → ℂ) (ψ : H) :
    err i M ψ = ∑ p : Bool, ∑ q : Bool, coef M p q • Pauli (pu i p) (pu i q) ψ := by
  funext v
  have hset0 : setq v i (v i) = v := by
    funext q; simp only [setq]; split <;> simp_all
  have hset1 : setq v i (!(v i)) = xr v (uc i) := by
    funext q
    simp only [setq, xr, uc]
    by_cases h : q = i
    · subst h; simp
    · simp [h]
  have hxr : (xr v (uc i)) i = !(v i) := by simp [xr]
  simp only [err, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_bool, Finset.sum_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pauli_apply, pu, if_true, if_false,
    Bool.false_eq_true, xr_zc, zph_zc_left, zph_uc, one_mul]
  rw [hxr]
  cases h : v i
  · rw [h] at hset0
    simp only [h, Bool.not_false] at hset1 ⊢
    rw [hset0, hset1]
    simp only [coef, sg_false, sg_true]
    ring
  · rw [h] at hset0
    simp only [h, Bool.not_true] at hset1 ⊢
    rw [hset0, hset1]
    simp only [coef, sg_false, sg_true]
    ring

lemma err_L_expand (i : Qb) (M : Bool → Bool → ℂ) (b : Bool) :
    err i M (L b) = ∑ p : Bool, ∑ q : Bool, coef M p q • V (corr i p q, b) := by
  rw [err_L]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
    rw [Pauli_pu_L]

/-! ## The recovery channel -/

/-- Orthogonal projection onto the span of the corrupted code states. -/
def Qp : H →ₗ[ℂ] H where
  toFun φ := ∑ m : J × Bool, ip (V m) φ • V m
  map_add' := by
    intro x y
    simp only [ip_add_right, add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [ip_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]

lemma Qp_apply (φ : H) : Qp φ = ∑ m : J × Bool, ip (V m) φ • V m := rfl

lemma Qp_V (n : J × Bool) : Qp (V n) = V n := by
  rw [Qp_apply]
  simp only [V_orthonormal, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ n V, if_pos (Finset.mem_univ n)]

/-- Kraus operators of the recovery channel: one for each correctable error class,
plus a "no correction possible" operator, which annihilates every corrupted code state. -/
def R : Option J → (H →ₗ[ℂ] H)
  | some j =>
      { toFun := fun φ => ip (V (j, false)) φ • L false + ip (V (j, true)) φ • L true
        map_add' := by
          intro x y; simp only [ip_add_right, add_smul]; abel
        map_smul' := by
          intro c x
          simp only [ip_smul_right, RingHom.id_apply, smul_add, smul_smul] }
  | none => LinearMap.id - Qp

lemma R_some (j : J) (φ : H) :
    R (some j) φ = ip (V (j, false)) φ • L false + ip (V (j, true)) φ • L true := rfl

lemma R_none (φ : H) : R none φ = φ - Qp φ := rfl

/-! ## Orthonormality of the logical basis -/

lemma L_orthonormal (a b : Bool) : ip (L a) (L b) = if a = b then 1 else 0 := by
  have := ip_key a b zc zc (Or.inr ⟨rfl, by decide⟩)
  rw [Pauli_zc_zc] at this
  rw [this, if_pos ⟨rfl, by decide⟩]

/-! ## The channel identity -/

lemma bessel (φ : H) :
    ip (φ - Qp φ) (φ - Qp φ)
      + ∑ m : J × Bool, (starRingEnd ℂ) (ip (V m) φ) * ip (V m) φ = ip φ φ := by
  have h2 : ip (Qp φ) φ = ∑ m : J × Bool, (starRingEnd ℂ) (ip (V m) φ) * ip (V m) φ := by
    rw [Qp_apply, ip_sum_left]
    exact Finset.sum_congr rfl fun m _ => ip_smul_left _ _ _
  have h1 : ip φ (Qp φ) = ∑ m : J × Bool, (starRingEnd ℂ) (ip (V m) φ) * ip (V m) φ := by
    rw [Qp_apply, ip_sum_right]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ip_smul_right, ← ip_conj (V m) φ]
    ring
  have hQ : ip (Qp φ) (Qp φ) = ∑ m : J × Bool, (starRingEnd ℂ) (ip (V m) φ) * ip (V m) φ := by
    rw [Qp_apply, ip_sum_left]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ip_smul_left, ip_sum_right]
    have hin : ∀ n : J × Bool,
        ip (V m) (ip (V n) φ • V n) = if m = n then ip (V n) φ else 0 := by
      intro n
      rw [ip_smul_right, V_orthonormal]
      split <;> simp
    rw [Finset.sum_congr rfl (fun n _ => hin n),
      Finset.sum_ite_eq Finset.univ m (fun n => ip (V n) φ), if_pos (Finset.mem_univ m)]
  rw [ip_sub_left, ip_sub_right, ip_sub_right, h1, h2, hQ]
  ring

/-! ## Main theorem

The 9-qubit Shor code corrects an arbitrary single-qubit error:

* the two logical states `L false`, `L true` are orthonormal, so the code space is a
  genuine qubit;
* the family `R` of Kraus operators is trace preserving, i.e. it is a quantum channel
  (`∑ s, ‖R s φ‖² = ‖φ‖²` for every state `φ`);
* for **every** qubit `i`, **every** single-qubit operator `M` (an arbitrary complex
  `2 × 2` matrix, hence an arbitrary Kraus operator of an arbitrary single-qubit noise
  channel) and every branch `s` of the recovery, the recovery returns the original code
  state `α|0_L⟩ + β|1_L⟩` up to a scalar `c` that does not depend on the encoded state.
  Hence the recovery channel restores the encoded state exactly.
-/
theorem shor_code_corrects :
    (∀ a b : Bool, ip (L a) (L b) = if a = b then 1 else 0) ∧
    (∀ φ : H, ∑ s : Option J, ip (R s φ) (R s φ) = ip φ φ) ∧
    (∀ (i : Qb) (M : Bool → Bool → ℂ) (s : Option J), ∃ c : ℂ, ∀ α β : ℂ,
        R s (err i M (α • L false + β • L true)) = c • (α • L false + β • L true)) := by
  refine ⟨L_orthonormal, ?_, ?_⟩
  · -- trace preservation: the recovery is a quantum channel
    intro φ
    rw [Fintype.sum_option]
    have hsome : ∀ j : J, ip (R (some j) φ) (R (some j) φ)
        = (starRingEnd ℂ) (ip (V (j, false)) φ) * ip (V (j, false)) φ
          + (starRingEnd ℂ) (ip (V (j, true)) φ) * ip (V (j, true)) φ := by
      intro j
      rw [R_some]
      simp only [ip_add_left, ip_add_right, ip_smul_left, ip_smul_right, L_orthonormal]
      norm_num
      ring
    simp_rw [hsome, R_none]
    rw [← bessel φ]
    congr 1
    symm
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun j _ => by rw [Fintype.sum_bool]; ring
  · -- correction of an arbitrary single-qubit error
    intro i M s
    cases s with
    | none =>
        refine ⟨0, fun α β => ?_⟩
        rw [zero_smul, R_none, sub_eq_zero]
        have hexp : err i M (α • L false + β • L true)
            = α • (∑ p : Bool, ∑ q : Bool, coef M p q • V (corr i p q, false))
              + β • (∑ p : Bool, ∑ q : Bool, coef M p q • V (corr i p q, true)) := by
          rw [map_add, map_smul, map_smul, err_L_expand, err_L_expand]
        rw [hexp]
        simp only [map_add, map_smul, map_sum, Qp_V]
    | some j =>
        obtain ⟨cj, hcj⟩ : ∃ c : ℂ,
            c = ∑ p : Bool, ∑ q : Bool, (if corr i p q = j then coef M p q else 0) := ⟨_, rfl⟩
        refine ⟨cj, fun α β => ?_⟩
        have hip : ∀ a : Bool, ip (V (j, a)) (err i M (α • L false + β • L true))
            = (bif a then β else α) * cj := by
          intro a
          rw [map_add, map_smul, map_smul, err_L_expand, err_L_expand,
            ip_add_right, ip_smul_right, ip_smul_right]
          have key : ∀ b : Bool,
              ip (V (j, a)) (∑ p : Bool, ∑ q : Bool, coef M p q • V (corr i p q, b))
                = if b = a then cj else 0 := by
            intro b
            rw [ip_sum_right]
            have hp : ∀ p : Bool, ip (V (j, a)) (∑ q : Bool, coef M p q • V (corr i p q, b))
                = ∑ q : Bool,
                    (if b = a then (if corr i p q = j then coef M p q else 0) else 0) := by
              intro p
              rw [ip_sum_right]
              refine Finset.sum_congr rfl fun q _ => ?_
              rw [ip_smul_right, V_orthonormal]
              simp only [Prod.mk.injEq]
              by_cases hb : b = a
              · subst hb
                by_cases hq : corr i p q = j
                · simp [hq]
                · simp [hq, Ne.symm hq]
              · simp [hb, Ne.symm hb]
            rw [Finset.sum_congr rfl (fun p _ => hp p)]
            by_cases hb : b = a
            · simp [hb, hcj]
            · simp [hb]
          rw [key, key]
          cases a
          · simp
          · simp
        rw [R_some, hip, hip]
        simp only [cond_false, cond_true, smul_add, smul_smul]
        rw [mul_comm α cj, mul_comm β cj]

end

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

