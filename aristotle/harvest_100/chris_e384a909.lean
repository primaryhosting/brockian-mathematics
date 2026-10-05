/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above
-- is written as a plain block comment; it is repeated as a module docstring below.)

import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
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

namespace QI

/-! ## Setup

The nine qubits of the Shor code are indexed by `Idx = Fin 3 × Fin 3`: the first
component is the block (of the outer phase-flip code), the second the position
inside the block (the inner bit-flip repetition code).

A computational basis state is a configuration `Cfg = Idx → Bool`, and a state
vector is a function `St = Cfg → ℂ` giving the amplitude of each basis state.
-/

/-- Index set of the nine qubits: `(block, position)`. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- A computational basis label for the nine qubits. -/
abbrev Cfg : Type := Idx → Bool

/-- A state vector of the nine-qubit register. -/
abbrev St : Type := Cfg → ℂ

/-- The standard hermitian inner product on the nine-qubit state space,
antilinear in the first argument. -/
noncomputable def ip (f g : St) : ℂ := ∑ x : Cfg, star (f x) * g x

/-- Bitwise `xor` of two configurations. -/
def xorCfg (x p : Cfg) : Cfg := fun k => xor (x k) (p k)

/-- The configuration which is `b` at qubit `i` and `false` elsewhere. -/
def sing (i : Idx) (b : Bool) : Cfg := fun k => if k = i then b else false

/-- The sign `(-1)^(q · x)` produced by the phase-flip part `Z^q` of a Pauli
operator acting on the basis state `x`. -/
def zsI (q x : Cfg) : ℤ := ∏ k : Idx, (if q k && x k then -1 else 1)

/-- Amplitude of one block of three qubits inside the (unnormalized) codeword:
`|000⟩ + (-1)^u |111⟩`. -/
def bAmp (u : Bool) (z : Fin 3 → Bool) : ℤ :=
  if z 0 = z 1 ∧ z 1 = z 2 then (if z 0 && u then -1 else 1) else 0

/-- Amplitude of the basis state `x` in the unnormalized logical codeword
`(|000⟩ + (-1)^u|111⟩)^⊗3`. -/
def wI (u : Bool) (x : Cfg) : ℤ := ∏ b : Fin 3, bAmp u (fun p => x (b, p))

/-- The two logical codewords of the nine-qubit Shor code:
`cw false = |0_L⟩ = (1/(2√2)) (|000⟩+|111⟩)^⊗3`,
`cw true  = |1_L⟩ = (1/(2√2)) (|000⟩-|111⟩)^⊗3`. -/
noncomputable def cw (u : Bool) : St := fun x => (2 * Real.sqrt 2)⁻¹ * (wI u x : ℂ)

/-- An arbitrary single-qubit operator `M` (a `2 × 2` complex matrix) acting on
qubit `i` of the nine-qubit register, i.e. `M ⊗ I` on the remaining qubits. -/
noncomputable def qop (i : Idx) (M : Matrix Bool Bool ℂ) (f : St) : St :=
  fun x => ∑ b : Bool, M (x i) b * f (Function.update x i b)

/-- The Pauli operator `X^p Z^q` on the nine-qubit register. -/
noncomputable def pauliOp (p q : Cfg) (f : St) : St :=
  fun x => (zsI q (xorCfg x p) : ℂ) * f (xorCfg x p)

/-- The single-qubit Pauli `X^pb Z^qb` acting on qubit `i`. -/
noncomputable def sq (i : Idx) (pb qb : Bool) (f : St) : St :=
  pauliOp (sing i pb) (sing i qb) f

/-- Coefficient of `X^p Z^q` in the Pauli expansion of the `2 × 2` matrix `M`. -/
noncomputable def pcoef (M : Matrix Bool Bool ℂ) (p q : Bool) : ℂ :=
  (M p false + (if q then -1 else 1) * M (!p) true) / 2

/-! ## Basic combinatorics of the code space -/

/-- A configuration is *block constant* if it is constant on each block of three
qubits; these are exactly the basis states occurring in the codewords. -/
def BC (x : Cfg) : Prop := ∀ (b p p' : Fin 3), x (b, p) = x (b, p')

lemma bAmp_ne_zero_const {u : Bool} {z : Fin 3 → Bool} (h : bAmp u z ≠ 0) :
    ∀ p p' : Fin 3, z p = z p' := by
  by_cases hz : z 0 = z 1 ∧ z 1 = z 2
  · intro p p'
    obtain ⟨h1, h2⟩ := hz
    fin_cases p <;> fin_cases p' <;> simp_all
  · exact absurd (by simp [bAmp, hz]) h

lemma wI_ne_zero_BC {u : Bool} {x : Cfg} (h : wI u x ≠ 0) : BC x := by
  intro b p p'
  have := Finset.prod_ne_zero_iff.mp (by simpa [wI] using h) b (Finset.mem_univ b)
  exact bAmp_ne_zero_const this p p'

lemma BC_xor {y y' : Cfg} (h : BC y) (h' : BC y') : BC (xorCfg y y') := by
  intro b p p'
  simp [xorCfg, h b p p', h' b p p']

/-- In every block there is a position distinct from two given qubits. -/
lemma exists_free_pos (b : Fin 3) (i j : Idx) :
    ∃ p : Fin 3, (b, p) ≠ i ∧ (b, p) ≠ j := by
  revert b i j; decide

/-- A block-constant configuration supported on at most two qubits is zero. -/
lemma BC_supp_eq_zero {d : Cfg} {i j : Idx} (hbc : BC d)
    (hsupp : ∀ k, d k = true → k = i ∨ k = j) : d = fun _ => false := by
  funext k
  obtain ⟨b, p⟩ := k
  obtain ⟨p0, hp0i, hp0j⟩ := exists_free_pos b i j
  have h0 : d (b, p0) = false := by
    by_contra hne
    rcases hsupp (b, p0) (by simpa using hne) with h | h
    · exact hp0i h
    · exact hp0j h
  rw [hbc b p p0, h0]

/-! ## Pauli sign algebra -/

lemma zsI_mul (q q' x : Cfg) : zsI q x * zsI q' x = zsI (xorCfg q q') x := by
  rw [zsI, zsI, zsI, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  cases hq : q k <;> cases hq' : q' k <;> cases hx : x k <;> simp [xorCfg, hq, hq']

lemma zsI_sing (i : Idx) (qb : Bool) (y : Cfg) :
    zsI (sing i qb) y = if qb && y i then -1 else 1 := by
  rw [zsI, Finset.prod_eq_single i]
  · simp [sing]
  · intro k _ hk; simp [sing, hk]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ## Sesquilinearity of the inner product -/

lemma ip_sum_sum {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → ℂ) (d : κ → ℂ) (F : ι → St) (G : κ → St) :
    ip (fun x => ∑ k, c k * F k x) (fun x => ∑ l, d l * G l x)
      = ∑ k, ∑ l, star (c k) * d l * ip (F k) (G l) := by
  have key : ∀ x : Cfg, star ((∑ k, c k * F k x)) * (∑ l, d l * G l x)
      = ∑ k, ∑ l, (star (c k) * d l) * (star (F k x) * G l x) := by
    intro x
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_mul']
    ring
  simp only [ip, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]

/-! ## The Pauli expansion of a single-qubit operator -/

lemma matrix_pauli_expansion (M : Matrix Bool Bool ℂ) (a b : Bool) :
    M a b = ∑ q : Bool, pcoef M (xor a b) q * (if q && b then -1 else 1) := by
  cases a <;> cases b <;> simp [pcoef] <;> ring

lemma xorCfg_sing (x : Cfg) (i : Idx) (pb : Bool) :
    xorCfg x (sing i pb) = Function.update x i (xor (x i) pb) := by
  funext k
  by_cases h : k = i
  · subst h; simp [xorCfg, sing]
  · simp [xorCfg, sing, h]

lemma sq_apply (i : Idx) (pb qb : Bool) (f : St) (x : Cfg) :
    sq i pb qb f x
      = (if qb && xor (x i) pb then (-1 : ℂ) else 1)
          * f (Function.update x i (xor (x i) pb)) := by
  rw [sq, pauliOp, xorCfg_sing, zsI_sing]
  simp [Function.update_self, apply_ite (fun t : ℤ => (t : ℂ))]

lemma qop_eq_sum (i : Idx) (M : Matrix Bool Bool ℂ) (f : St) :
    qop i M f = fun x => ∑ k : Bool × Bool, pcoef M k.1 k.2 * sq i k.1 k.2 f x := by
  funext x
  rw [qop]
  rw [Fintype.sum_prod_type]
  have step : ∀ pb : Bool,
      (∑ qb : Bool, pcoef M pb qb * sq i pb qb f x)
        = M (x i) (xor (x i) pb) * f (Function.update x i (xor (x i) pb)) := by
    intro pb
    have hM : M (x i) (xor (x i) pb)
        = ∑ qb : Bool, pcoef M pb qb * (if qb && xor (x i) pb then (-1 : ℂ) else 1) := by
      have := matrix_pauli_expansion M (x i) (xor (x i) pb)
      simpa [Bool.xor_left_comm] using this
    rw [hM, Finset.sum_mul]
    refine Finset.sum_congr rfl fun qb _ => ?_
    rw [sq_apply]
    ring
  rw [Finset.sum_congr rfl (fun pb (_ : pb ∈ Finset.univ) => step pb)]
  cases x i
  · simp
  · simp
    ring

/-! ## The key inner-product computations -/

/-- The integer core of the inner product `⟨w_u| Z^r |w_v⟩`. -/
def Dsum (r : Cfg) (u v : Bool) : ℤ := ∑ x : Cfg, zsI r x * wI u x * wI v x

/-- The per-block contribution to `Dsum`. -/
def Sblk (rho : Fin 3 → Bool) (u v : Bool) : ℤ :=
  ∑ z : Fin 3 → Bool, (∏ p : Fin 3, if rho p && z p then -1 else 1) * bAmp u z * bAmp v z

lemma Dsum_prod (r : Cfg) (u v : Bool) :
    Dsum r u v = ∏ b : Fin 3, Sblk (fun p => r (b, p)) u v := by
  set g : Fin 3 → (Fin 3 → Bool) → ℤ := fun b z =>
    (∏ p : Fin 3, if r (b, p) && z p then (-1 : ℤ) else 1) * bAmp u z * bAmp v z with hg
  have h1 : ∀ x : Cfg, zsI r x * wI u x * wI v x = ∏ b : Fin 3, g b (fun p => x (b, p)) := by
    intro x
    simp only [hg, Finset.prod_mul_distrib]
    congr 1
    congr 1
    · rw [zsI, Fintype.prod_prod_type]
  have h2 : (∑ x : Cfg, ∏ b : Fin 3, g b (fun p => x (b, p)))
      = ∑ y : Fin 3 → Fin 3 → Bool, ∏ b : Fin 3, g b (y b) :=
    Fintype.sum_equiv (Equiv.curry (Fin 3) (Fin 3) Bool) _ _ (fun _ => rfl)
  have h3 : (∏ b : Fin 3, Sblk (fun p => r (b, p)) u v)
      = ∑ y : Fin 3 → Fin 3 → Bool, ∏ b : Fin 3, g b (y b) := by
    have := Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (Fin 3 → Bool))) g
    rw [Fintype.piFinset_univ] at this
    simpa [Sblk, hg] using this
  rw [Dsum, Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => h1 x), h2, h3]

lemma Sblk_diag (rho : Fin 3 → Bool) : Sblk rho false false = Sblk rho true true := by
  revert rho; decide

lemma Sblk_zero_off (u v : Bool) (huv : u ≠ v) : Sblk (fun _ => false) u v = 0 := by
  revert u v; decide

lemma Dsum_diag (r : Cfg) : Dsum r false false = Dsum r true true := by
  rw [Dsum_prod, Dsum_prod]
  exact Finset.prod_congr rfl fun b _ => Sblk_diag _

/-- Among three blocks, one avoids two given qubits. -/
lemma exists_free_block (i j : Idx) : ∃ b : Fin 3, b ≠ i.1 ∧ b ≠ j.1 := by
  revert i j; decide

lemma Dsum_off_eq_zero {r : Cfg} {i j : Idx} (hsupp : ∀ k, r k = true → k = i ∨ k = j)
    {u v : Bool} (huv : u ≠ v) : Dsum r u v = 0 := by
  obtain ⟨b, hbi, hbj⟩ := exists_free_block i j
  have hzero : (fun p => r (b, p)) = (fun _ : Fin 3 => false) := by
    funext p
    by_contra hne
    rcases hsupp (b, p) (by simpa using hne) with h | h
    · exact hbi (congrArg Prod.fst h)
    · exact hbj (congrArg Prod.fst h)
  rw [Dsum_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
  rw [hzero]
  exact Sblk_zero_off u v huv

lemma xorCfg_involutive (p : Cfg) : Function.Involutive (fun x : Cfg => xorCfg x p) := by
  intro x; funext k; simp [xorCfg]

/-- Inner product of two Pauli-rotated codewords with the same `X`-part. -/
lemma ip_pauli_same (p q q' : Cfg) (u v : Bool) :
    ip (pauliOp p q (cw u)) (pauliOp p q' (cw v))
      = ((2 * Real.sqrt 2)⁻¹ : ℝ)^2 * (Dsum (xorCfg q q') u v : ℂ) := by
  have hterm : ∀ x : Cfg, star (pauliOp p q (cw u) x) * pauliOp p q' (cw v) x
      = ((2 * Real.sqrt 2)⁻¹ : ℝ)^2 *
        ((zsI (xorCfg q q') (xorCfg x p) * wI u (xorCfg x p) * wI v (xorCfg x p) : ℤ) : ℂ) := by
    intro x
    rw [← zsI_mul]
    simp only [pauliOp, cw, star_mul', Complex.star_def, Complex.conj_ofReal,
      map_intCast, Int.cast_mul]
    push_cast
    ring
  rw [ip, Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hterm x), ← Finset.mul_sum]
  congr 1
  rw [Dsum, Int.cast_sum]
  exact Equiv.sum_comp (Function.Involutive.toPerm _ (xorCfg_involutive p))
    (fun y => ((zsI (xorCfg q q') y * wI u y * wI v y : ℤ) : ℂ))

/-- If the `X`-parts differ, the codewords are moved to orthogonal sets of basis
states. -/
lemma ip_pauli_diff {p p' : Cfg} (q q' : Cfg) {i j : Idx}
    (hi : ∀ k, p k = true → k = i) (hj : ∀ k, p' k = true → k = j)
    (hne : p ≠ p') (u v : Bool) :
    ip (pauliOp p q (cw u)) (pauliOp p' q' (cw v)) = 0 := by
  rw [ip]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hu : wI u (xorCfg x p) = 0
  · simp [pauliOp, cw, hu]
  by_cases hv : wI v (xorCfg x p') = 0
  · simp [pauliOp, cw, hv]
  exfalso
  have hbc : BC (xorCfg (xorCfg x p) (xorCfg x p')) :=
    BC_xor (wI_ne_zero_BC hu) (wI_ne_zero_BC hv)
  have hd : xorCfg (xorCfg x p) (xorCfg x p') = xorCfg p p' := by
    funext k
    simp only [xorCfg]
    cases x k <;> cases p k <;> cases p' k <;> rfl
  rw [hd] at hbc
  have hsupp : ∀ k, xorCfg p p' k = true → k = i ∨ k = j := by
    intro k hk
    by_cases h1 : p k = true
    · exact Or.inl (hi k h1)
    · have : p' k = true := by
        simp only [xorCfg] at hk
        cases hp : p k <;> cases hp' : p' k <;> simp_all
      exact Or.inr (hj k this)
  have := BC_supp_eq_zero hbc hsupp
  refine hne (funext fun k => ?_)
  have hk := congrFun this k
  simp only [xorCfg] at hk
  cases hp : p k <;> cases hp' : p' k <;> simp_all

/-! ## Knill–Laflamme conditions for single-qubit Paulis -/

lemma sing_supp (i : Idx) (b : Bool) : ∀ k, sing i b k = true → k = i := by
  intro k hk
  by_contra h
  simp [sing, h] at hk

lemma xor_sing_supp (i j : Idx) (qb qb' : Bool) :
    ∀ k, xorCfg (sing i qb) (sing j qb') k = true → k = i ∨ k = j := by
  intro k hk
  by_cases h1 : k = i
  · exact Or.inl h1
  by_cases h2 : k = j
  · exact Or.inr h2
  simp [xorCfg, sing, h1, h2] at hk

lemma key_off (i j : Idx) (pb qb pb' qb' : Bool) {u v : Bool} (huv : u ≠ v) :
    ip (sq i pb qb (cw u)) (sq j pb' qb' (cw v)) = 0 := by
  rw [sq, sq]
  by_cases h : sing i pb = sing j pb'
  · rw [← h, ip_pauli_same, Dsum_off_eq_zero (xor_sing_supp i j qb qb') huv]
    simp
  · exact ip_pauli_diff _ _ (sing_supp i pb) (sing_supp j pb') h u v

lemma key_diag (i j : Idx) (pb qb pb' qb' : Bool) :
    ip (sq i pb qb (cw false)) (sq j pb' qb' (cw false))
      = ip (sq i pb qb (cw true)) (sq j pb' qb' (cw true)) := by
  rw [sq, sq, sq, sq]
  by_cases h : sing i pb = sing j pb'
  · rw [← h, ip_pauli_same, ip_pauli_same, Dsum_diag]
  · rw [ip_pauli_diff _ _ (sing_supp i pb) (sing_supp j pb') h,
      ip_pauli_diff _ _ (sing_supp i pb) (sing_supp j pb') h]

/-! ## Normalization -/

lemma pauliOp_zero (f : St) : pauliOp (fun _ : Idx => false) (fun _ : Idx => false) f = f := by
  funext x
  have hx : xorCfg x (fun _ : Idx => false) = x := by funext k; simp [xorCfg]
  simp [pauliOp, hx, zsI]

lemma kappa_sq : ((2 * Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 8 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [inv_pow, mul_pow, h]
  norm_num

lemma kappa_sq_C : ((((2 : ℝ) * Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2 = 1 / 8 := by
  have hcast : ((((2 : ℝ) * Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2
      = (((((2 : ℝ) * Real.sqrt 2)⁻¹) ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, kappa_sq]
  norm_num

lemma Dsum_zero_diag (u : Bool) : Dsum (fun _ : Idx => false) u u = 8 := by
  rw [Dsum_prod]
  have hb : Sblk (fun _ : Fin 3 => false) u u = 2 := by revert u; decide
  simp only [hb, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-! ## Main theorem -/

/--
**The nine-qubit Shor code corrects an arbitrary single-qubit error.**

`cw false` and `cw true` are the two logical codewords of the Shor code.  For
any two qubits `i, j` and any single-qubit operators `M, N` (arbitrary `2 × 2`
complex matrices, acting on qubit `i` resp. `j` and as the identity elsewhere)
the Knill–Laflamme error-correction conditions hold: there is a constant `c`,
independent of the logical states, with
`⟨M_i w_u , N_j w_v⟩ = ⟨w_u| M_i^† N_j |w_v⟩ = c · δ_{u,v}`.

Since every single-qubit error channel has Kraus operators of this form, and the
conditions are (sesqui)linear in the error operators, this is exactly the
necessary and sufficient criterion for the existence of a recovery operation
correcting an arbitrary error on any one of the nine qubits.
-/
theorem shor_code_corrects (i j : Idx) (M N : Matrix Bool Bool ℂ) :
    ∃ c : ℂ, ∀ u v : Bool,
      ip (qop i M (cw u)) (qop j N (cw v)) = if u = v then c else 0 := by
  have expand : ∀ u v : Bool, ip (qop i M (cw u)) (qop j N (cw v))
      = ∑ k : Bool × Bool, ∑ l : Bool × Bool,
          star (pcoef M k.1 k.2) * pcoef N l.1 l.2
            * ip (sq i k.1 k.2 (cw u)) (sq j l.1 l.2 (cw v)) := by
    intro u v
    rw [qop_eq_sum i M, qop_eq_sum j N]
    exact ip_sum_sum (fun k : Bool × Bool => pcoef M k.1 k.2)
      (fun l : Bool × Bool => pcoef N l.1 l.2)
      (fun k : Bool × Bool => sq i k.1 k.2 (cw u)) (fun l : Bool × Bool => sq j l.1 l.2 (cw v))
  refine ⟨ip (qop i M (cw false)) (qop j N (cw false)), ?_⟩
  intro u v
  cases u <;> cases v
  · simp
  · rw [if_neg (by simp), expand]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    rw [key_off i j k.1 k.2 l.1 l.2 (by simp), mul_zero]
  · rw [if_neg (by simp), expand]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    rw [key_off i j k.1 k.2 l.1 l.2 (by simp), mul_zero]
  · rw [if_pos rfl, expand true true, expand false false]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [key_diag i j k.1 k.2 l.1 l.2]

/-- The two logical codewords are orthonormal, so the code space is a qubit. -/
theorem shor_codewords_orthonormal (u v : Bool) :
    ip (cw u) (cw v) = if u = v then 1 else 0 := by
  have hzz : xorCfg (fun _ : Idx => false) (fun _ : Idx => false) = (fun _ : Idx => false) := by
    funext k; simp [xorCfg]
  have h := ip_pauli_same (fun _ : Idx => false) (fun _ : Idx => false) (fun _ : Idx => false) u v
  rw [pauliOp_zero, pauliOp_zero, hzz, kappa_sq_C] at h
  rw [h]
  cases u <;> cases v
  · rw [Dsum_zero_diag]; norm_num
  · rw [Dsum_off_eq_zero (i := (0, 0)) (j := (0, 0)) (by intro k hk; simp at hk) (by simp)]
    simp
  · rw [Dsum_off_eq_zero (i := (0, 0)) (j := (0, 0)) (by intro k hk; simp at hk) (by simp)]
    simp
  · rw [Dsum_zero_diag]; norm_num

end QI

