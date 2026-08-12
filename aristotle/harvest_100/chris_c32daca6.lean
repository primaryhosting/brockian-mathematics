/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace QI

/-- Index set of the nine qubits: three blocks of three. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits are bit strings. -/
abbrev Bits : Type := Idx → Bool

/-- Pointwise `xor` of two bit strings. -/
def bxor (a b : Bits) : Bits := fun q => xor (a q) (b q)

/-- The all-zero bit string. -/
def bzero : Bits := fun _ => false

/-- The bit string with a single `1` at position `k`. -/
def bone (k : Idx) : Bits := fun q => decide (q = k)

/-- The sign `(-1)^(u ⬝ v)` attached to a `Z`-type Pauli `u` on the basis state `v`. -/
def chi (u v : Bits) : ℤ := ∏ q : Idx, (if u q && v q then (-1 : ℤ) else 1)

/-- A bit string is *blocky* when it is constant on each of the three blocks. -/
def Blocky (b : Bits) : Prop := ∀ q : Idx, b q = b (q.1, 0)

instance (b : Bits) : Decidable (Blocky b) := by unfold Blocky; infer_instance

/-- The blocky bit string determined by the three block values. -/
def expand (t : Fin 3 → Bool) : Bits := fun q => t q.1

/-- Unnormalized amplitudes of the two logical states of the Shor code:
`f false` is `(|000⟩+|111⟩)^{⊗3}` and `f true` is `(|000⟩-|111⟩)^{⊗3}`. -/
def f (a : Bool) (c : Bits) : ℤ :=
  if Blocky c then (if a then ∏ m : Fin 3, (if c (m, 0) then (-1 : ℤ) else 1) else 1) else 0

/-- Normalisation constant `1/√8`. -/
noncomputable def nrm : ℝ := (Real.sqrt 8)⁻¹

/-- The two logical basis states of the nine-qubit Shor code. -/
noncomputable def psi (a : Bool) : Bits → ℂ := fun c => (nrm : ℂ) * (f a c : ℂ)

/-- Hermitian inner product on the `2^9`-dimensional state space. -/
noncomputable def ip (φ ψ : Bits → ℂ) : ℂ := ∑ v : Bits, (starRingEnd ℂ) (φ v) * ψ v

/-- The Pauli operator `Z^z X^x`. -/
noncomputable def pauli (x z : Bits) (ψ : Bits → ℂ) : Bits → ℂ := fun v => (chi z v : ℂ) * ψ (bxor v x)

/-- An arbitrary single-qubit operator `M` acting on qubit `k` (tensored with the identity
on the remaining eight qubits). -/
noncomputable def applyOp (k : Idx) (M : Bool → Bool → ℂ) (ψ : Bits → ℂ) : Bits → ℂ :=
  fun v => ∑ s : Bool, M (v k) s * ψ (Function.update v k s)

/-! ## Basic algebra of bit strings and signs -/

@[simp] lemma bxor_bzero (v : Bits) : bxor v bzero = v := by
  funext q; simp [bxor, bzero]

lemma bxor_comm (a b : Bits) : bxor a b = bxor b a := by
  funext q; simp [bxor, Bool.xor_comm]

lemma bxor_assoc (a b c : Bits) : bxor (bxor a b) c = bxor a (bxor b c) := by
  funext q; simp [bxor]

@[simp] lemma bxor_self_cancel (v x : Bits) : bxor (bxor v x) x = v := by
  funext q; simp [bxor]

lemma bxor_eq_bzero_iff (a b : Bits) : bxor a b = bzero ↔ a = b := by
  constructor
  · intro h
    funext q
    have := congrFun h q
    simp [bxor, bzero] at this
    revert this
    cases a q <;> cases b q <;> simp
  · intro h; subst h; funext q; simp [bxor, bzero]

/-- Bookkeeping identity for signs. -/
lemma sign_xor (a b c : Bool) :
    (if (xor a b) && c then (-1 : ℤ) else 1)
      = (if a && c then (-1 : ℤ) else 1) * (if b && c then (-1 : ℤ) else 1) := by
  revert a b c; decide

/-- Bookkeeping identity for signs. -/
lemma sign_xor' (a b c : Bool) :
    (if a && (xor b c) then (-1 : ℤ) else 1)
      = (if a && b then (-1 : ℤ) else 1) * (if a && c then (-1 : ℤ) else 1) := by
  revert a b c; decide

/-- Bookkeeping identity for signs. -/
lemma sign_three (a b c s : Bool) :
    ((if a && s then (-1 : ℤ) else 1) * (if b && s then (-1 : ℤ) else 1))
        * (if c && s then (-1 : ℤ) else 1)
      = if s && (xor (xor a b) c) then (-1 : ℤ) else 1 := by
  revert a b c s; decide

/-- Bookkeeping identity for signs. -/
lemma sign_merge3 (s w1 ea eb : Bool) :
    ((if s && w1 then (-1 : ℤ) else 1) * (if s && ea then (-1 : ℤ) else 1))
        * (if s && eb then (-1 : ℤ) else 1)
      = if s && (xor w1 (xor ea eb)) then (-1 : ℤ) else 1 := by
  revert s w1 ea eb; decide

lemma chi_bxor_left (u u' v : Bits) : chi (bxor u u') v = chi u v * chi u' v := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun q _ => sign_xor (u q) (u' q) (v q))

lemma chi_bxor_right (u v x : Bits) : chi u (bxor v x) = chi u v * chi u x := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun q _ => sign_xor' (u q) (v q) (x q))

@[simp] lemma chi_bzero (v : Bits) : chi bzero v = 1 := by
  simp [chi, bzero]

/-! ## Blocky strings -/

lemma blocky_expand (t : Fin 3 → Bool) : Blocky (expand t) := by
  intro q; rfl

lemma expand_injective : Function.Injective expand := by
  intro t t' h
  funext m
  exact congrFun h (m, 0)

lemma expand_proj_of_blocky {c : Bits} (h : Blocky c) : expand (fun m => c (m, 0)) = c := by
  funext q; exact (h q).symm

lemma blocky_bxor {a b : Bits} (ha : Blocky a) (hb : Blocky b) : Blocky (bxor a b) := by
  intro q; simp [bxor, ha q, hb q]

lemma f_eq_zero_of_not_blocky (a : Bool) {c : Bits} (h : ¬ Blocky c) : f a c = 0 := by
  simp [f, h]

lemma f_expand (a : Bool) (t : Fin 3 → Bool) :
    f a (expand t) = if a then ∏ m : Fin 3, (if t m then (-1 : ℤ) else 1) else 1 := by
  simp [f, blocky_expand, expand]

/-! ## Reindexing sums -/

lemma sum_bxor_shift (F : Bits → ℤ) (x : Bits) : ∑ v : Bits, F (bxor v x) = ∑ v : Bits, F v := by
  refine Fintype.sum_equiv
    (Equiv.mk (fun v => bxor v x) (fun v => bxor v x) (fun v => by simp) (fun v => by simp)) _ _ ?_
  intro v; rfl

lemma filter_blocky : (Finset.univ.filter Blocky) = Finset.image expand Finset.univ := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h; exact ⟨fun m => c (m, 0), expand_proj_of_blocky h⟩
  · rintro ⟨t, rfl⟩; exact blocky_expand t

lemma sum_blocky (F : Bits → ℤ) (h : ∀ c, ¬ Blocky c → F c = 0) :
    ∑ c : Bits, F c = ∑ t : Fin 3 → Bool, F (expand t) := by
  have h1 : ∑ c ∈ Finset.univ.filter Blocky, F c = ∑ c : Bits, F c := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro c _ hc
    exact h c (by simpa using hc)
  rw [← h1, filter_blocky, Finset.sum_image (fun t _ t' _ htt' => expand_injective htt')]

/-! ## Block parities -/

/-- Parity of the restriction of `u` to block `m`. -/
def wpar (u : Bits) (m : Fin 3) : Bool := xor (xor (u (m, 0)) (u (m, 1))) (u (m, 2))

lemma chi_expand (u : Bits) (t : Fin 3 → Bool) :
    chi u (expand t) = ∏ m : Fin 3, (if t m && wpar u m then (-1 : ℤ) else 1) := by
  unfold chi
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl ?_
  intro m _
  rw [Fin.prod_univ_three]
  exact sign_three (u (m, 0)) (u (m, 1)) (u (m, 2)) (t m)

lemma sum_sign_prod (a : Fin 3 → Bool) :
    (∑ t : Fin 3 → Bool, ∏ m : Fin 3, (if t m && a m then (-1 : ℤ) else 1))
      = ∏ m : Fin 3, (if a m then (0 : ℤ) else 2) := by
  have := Finset.prod_univ_sum (ι := Fin 3) (κ := fun _ => Bool) (fun _ => Finset.univ)
    (fun m s => (if s && a m then (-1 : ℤ) else 1))
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  refine Finset.prod_congr rfl ?_
  intro m _
  simp only [Fintype.sum_bool]
  cases a m <;> norm_num

/-! ## The core computation -/

/-- Turning a `±1` prefactor into the product form. -/
lemma prod_par (t : Fin 3 → Bool) (e : Bool) :
    (if e then ∏ m : Fin 3, (if t m then (-1 : ℤ) else 1) else 1)
      = ∏ m : Fin 3, (if t m && e then (-1 : ℤ) else 1) := by
  cases e <;> simp

/-- The basic sum: `T u a b = ∑_c χ_u(c) f_a(c) f_b(c)`. -/
lemma T_eval (u : Bits) (a b : Bool) :
    (∑ c : Bits, chi u c * f a c * f b c)
      = ∏ m : Fin 3, (if xor (wpar u m) (xor a b) then (0 : ℤ) else 2) := by
  rw [sum_blocky _ (by intro c hc; simp [f_eq_zero_of_not_blocky _ hc])]
  have step : ∀ t : Fin 3 → Bool,
      chi u (expand t) * f a (expand t) * f b (expand t)
        = ∏ m : Fin 3, (if t m && (xor (wpar u m) (xor a b)) then (-1 : ℤ) else 1) := by
    intro t
    rw [chi_expand, f_expand, f_expand, prod_par, prod_par, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun m _ => sign_merge3 (t m) (wpar u m) a b)
  rw [Finset.sum_congr rfl (fun t _ => step t), sum_sign_prod]

lemma S_shift (u x y : Bits) (a b : Bool) :
    (∑ v : Bits, chi u v * f a (bxor v x) * f b (bxor v y))
      = chi u x * ∑ c : Bits, chi u c * f a c * f b (bxor c (bxor x y)) := by
  rw [← sum_bxor_shift (fun v => chi u v * f a (bxor v x) * f b (bxor v y)) x, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [bxor_self_cancel, bxor_assoc, chi_bxor_right]
  ring

/-! ## Support conditions coming from single-qubit errors -/

lemma exists_fin3_ne (a b : Fin 3) : ∃ m : Fin 3, m ≠ a ∧ m ≠ b := by revert a b; decide

lemma bxor_cancel_left (c d : Bits) : bxor c (bxor c d) = d := by
  funext q; simp [bxor]

lemma exists_wpar_false {u : Bits} {k l : Idx} (h : ∀ q, u q = true → q = k ∨ q = l) :
    ∃ m : Fin 3, wpar u m = false := by
  obtain ⟨m, hm1, hm2⟩ := exists_fin3_ne k.1 l.1
  refine ⟨m, ?_⟩
  have key : ∀ p : Fin 3, u (m, p) = false := by
    intro p
    by_contra hp
    have hp' : u (m, p) = true := by simpa using hp
    rcases h _ hp' with h' | h'
    · exact hm1 (congrArg Prod.fst h')
    · exact hm2 (congrArg Prod.fst h')
  simp [wpar, key 0, key 1, key 2]

lemma not_blocky_of_support {d : Bits} {k l : Idx} (hd : d ≠ bzero)
    (h : ∀ q, d q = true → q = k ∨ q = l) : ¬ Blocky d := by
  intro hb
  obtain ⟨q0, hq0⟩ : ∃ q, d q = true := by
    by_contra hcon
    push_neg at hcon
    exact hd (funext fun q => Bool.eq_false_iff.mpr (hcon q))
  obtain ⟨m, p0⟩ := q0
  have hbase : d (m, 0) = true := by rw [← hb (m, p0)]; exact hq0
  have h1 : d (m, 1) = true := by rw [hb (m, 1)]; exact hbase
  have h2 : d (m, 2) = true := by rw [hb (m, 2)]; exact hbase
  have hne : ∀ (p p' : Fin 3), ((m, p) : Idx) = (m, p') → p = p' :=
    fun p p' hpp => congrArg Prod.snd hpp
  rcases h _ hbase with e0 | e0 <;> rcases h _ h1 with e1 | e1 <;> rcases h _ h2 with e2 | e2 <;>
    first
      | exact absurd (hne 0 1 (e0.trans e1.symm)) (by decide)
      | exact absurd (hne 0 2 (e0.trans e2.symm)) (by decide)
      | exact absurd (hne 1 2 (e1.trans e2.symm)) (by decide)

/-! ## The two cases of the core sum -/

lemma f_mul_shift_eq_zero {d : Bits} (hd : ¬ Blocky d) (a b : Bool) (c : Bits) :
    f a c * f b (bxor c d) = 0 := by
  by_cases hc : Blocky c
  · by_cases hcd : Blocky (bxor c d)
    · exact absurd (bxor_cancel_left c d ▸ blocky_bxor hc hcd) hd
    · simp [f_eq_zero_of_not_blocky _ hcd]
  · simp [f_eq_zero_of_not_blocky _ hc]

lemma S_of_not_blocky (u x y : Bits) (a b : Bool) (hd : ¬ Blocky (bxor x y)) :
    (∑ v : Bits, chi u v * f a (bxor v x) * f b (bxor v y)) = 0 := by
  rw [S_shift]
  have : ∀ c : Bits, chi u c * f a c * f b (bxor c (bxor x y)) = 0 := by
    intro c
    rw [mul_assoc, f_mul_shift_eq_zero hd a b c, mul_zero]
  simp [Finset.sum_congr rfl (fun c _ => this c)]

lemma S_of_eq (u x : Bits) (a b : Bool) :
    (∑ v : Bits, chi u v * f a (bxor v x) * f b (bxor v x))
      = chi u x * ∏ m : Fin 3, (if xor (wpar u m) (xor a b) then (0 : ℤ) else 2) := by
  rw [S_shift]
  have hxx : bxor x x = bzero := by funext q; simp [bxor, bzero]
  simp only [hxx, bxor_bzero]
  rw [T_eval]

/-! ## From integer sums to inner products -/

lemma nrm_sq : nrm * nrm = 1 / 8 := by
  unfold nrm
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)]
  norm_num

lemma nrm_sq_complex : (nrm : ℂ) * (nrm : ℂ) = 1 / 8 := by
  rw [← Complex.ofReal_mul, nrm_sq]
  norm_num

lemma ip_pauli (x z x' z' : Bits) (a b : Bool) :
    ip (pauli x z (psi a)) (pauli x' z' (psi b))
      = (1 / 8 : ℂ)
        * ((∑ v : Bits, chi (bxor z z') v * f a (bxor v x) * f b (bxor v x') : ℤ) : ℂ) := by
  unfold ip pauli psi
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [chi_bxor_left]
  simp only [map_mul, Complex.conj_ofReal, map_intCast]
  push_cast
  rw [← nrm_sq_complex]
  ring

/-! ## Knill–Laflamme conditions for Pauli errors -/

lemma pauli_ip_core {k l : Idx} {x z x' z' : Bits}
    (hx : ∀ q, q ≠ k → x q = false) (hz : ∀ q, q ≠ k → z q = false)
    (hx' : ∀ q, q ≠ l → x' q = false) (hz' : ∀ q, q ≠ l → z' q = false) :
    (∀ a b : Bool, a ≠ b → ip (pauli x z (psi a)) (pauli x' z' (psi b)) = 0) ∧
      ip (pauli x z (psi true)) (pauli x' z' (psi true))
        = ip (pauli x z (psi false)) (pauli x' z' (psi false)) := by
  have hsuppu : ∀ q, (bxor z z') q = true → q = k ∨ q = l := by
    intro q hq
    by_contra hcon
    push_neg at hcon
    rw [bxor, hz q hcon.1, hz' q hcon.2] at hq
    exact Bool.noConfusion hq
  have hsuppd : ∀ q, (bxor x x') q = true → q = k ∨ q = l := by
    intro q hq
    by_contra hcon
    push_neg at hcon
    rw [bxor, hx q hcon.1, hx' q hcon.2] at hq
    exact Bool.noConfusion hq
  by_cases hd : bxor x x' = bzero
  · have hxx : x = x' := (bxor_eq_bzero_iff x x').1 hd
    subst hxx
    obtain ⟨m, hm⟩ := exists_wpar_false hsuppu
    constructor
    · intro a b hab
      rw [ip_pauli, S_of_eq]
      have hxorab : xor a b = true := by revert hab; revert a b; decide
      have hzero : (∏ m : Fin 3, (if xor (wpar (bxor z z') m) (xor a b) then (0 : ℤ) else 2)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ m) (by simp [hm, hxorab])
      rw [hzero]
      simp
    · rw [ip_pauli, ip_pauli, S_of_eq, S_of_eq]
      norm_num
  · have hnb : ¬ Blocky (bxor x x') := not_blocky_of_support hd hsuppd
    constructor
    · intro a b _
      rw [ip_pauli, S_of_not_blocky _ _ _ _ _ hnb]
      simp
    · rw [ip_pauli, ip_pauli, S_of_not_blocky _ _ _ _ _ hnb, S_of_not_blocky _ _ _ _ _ hnb]

/-! ## Orthonormality of the logical basis -/

lemma ip_psi (a b : Bool) : ip (psi a) (psi b) = if a = b then 1 else 0 := by
  have h0 : psi a = pauli bzero bzero (psi a) := by
    funext v; simp [pauli]
  have h1 : psi b = pauli bzero bzero (psi b) := by
    funext v; simp [pauli]
  rw [h0, h1, ip_pauli]
  have hzz : bxor bzero bzero = bzero := by funext q; simp [bxor, bzero]
  rw [hzz]
  have hs : (∑ v : Bits, chi bzero v * f a (bxor v bzero) * f b (bxor v bzero))
      = ∏ m : Fin 3, (if xor (wpar bzero m) (xor a b) then (0 : ℤ) else 2) := by
    have := S_of_eq bzero bzero a b
    simpa using this
  rw [hs]
  have hw : ∀ m : Fin 3, wpar bzero m = false := by intro m; simp [wpar, bzero]
  cases a <;> cases b <;> simp [hw]

/-! ## Expanding an arbitrary single-qubit operator in the Pauli basis -/

/-- `sel b k` is `e_k` if `b` is true, and the zero string otherwise. -/
def sel (b : Bool) (k : Idx) : Bits := if b then bone k else bzero

lemma sel_support (b : Bool) (k : Idx) : ∀ q, q ≠ k → sel b k q = false := by
  intro q hq
  cases b <;> simp [sel, bone, bzero, hq]

lemma chi_bone (k : Idx) (v : Bits) : chi (bone k) v = if v k then -1 else 1 := by
  unfold chi
  rw [Finset.prod_eq_single k]
  · simp [bone]
  · intro q _ hq; simp [bone, hq]
  · intro h; exact absurd (Finset.mem_univ k) h

lemma update_bxor (k : Idx) (v : Bits) : Function.update v k (! v k) = bxor v (bone k) := by
  funext q
  by_cases h : q = k
  · subst h; simp [bxor, bone]
  · simp [bxor, bone, h]

/-- The four Pauli coefficients of a `2 × 2` matrix `M`. -/
noncomputable def coefM (M : Bool → Bool → ℂ) : Bool × Bool → ℂ
  | (false, false) => (M false false + M true true) / 2
  | (true, false) => (M false true + M true false) / 2
  | (false, true) => (M false false - M true true) / 2
  | (true, true) => (M false true - M true false) / 2

lemma applyOp_eq (k : Idx) (M : Bool → Bool → ℂ) (ψ : Bits → ℂ) (v : Bits) :
    applyOp k M ψ v
      = ∑ p : Bool × Bool, coefM M p * pauli (sel p.1 k) (sel p.2 k) ψ v := by
  unfold applyOp
  rw [Fintype.sum_bool, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, pauli, sel, if_true, chi_bone, coefM]
  have hup : ∀ s : Bool, v k = s → Function.update v k s = v := by
    intro s hs; rw [← hs]; exact Function.update_eq_self k v
  have hupn : ∀ s : Bool, v k = !s → Function.update v k s = bxor v (bone k) := by
    intro s hs
    have : s = ! v k := by rw [hs]; simp
    rw [this, update_bxor]
  cases hv : v k
  · rw [hup false hv, hupn true (by simp [hv])]
    simp
    ring
  · rw [hup true hv, hupn false (by simp [hv])]
    simp
    ring

/-! ## Sesquilinearity of the inner product -/

lemma ip_sum_left {ι : Type} [Fintype ι] (F : ι → Bits → ℂ) (χ : Bits → ℂ) :
    ip (fun v => ∑ i, F i v) χ = ∑ i, ip (F i) χ := by
  unfold ip
  simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma ip_sum_right {κ : Type} [Fintype κ] (φ : Bits → ℂ) (G : κ → Bits → ℂ) :
    ip φ (fun v => ∑ j, G j v) = ∑ j, ip φ (G j) := by
  unfold ip
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma ip_sum_sum {ι κ : Type} [Fintype κ] [Fintype ι] (F : ι → Bits → ℂ) (G : κ → Bits → ℂ) :
    ip (fun v => ∑ i, F i v) (fun v => ∑ j, G j v) = ∑ i, ∑ j, ip (F i) (G j) := by
  rw [ip_sum_left]
  exact Finset.sum_congr rfl fun i _ => ip_sum_right _ _

lemma ip_smul_smul (c d : ℂ) (A B : Bits → ℂ) :
    ip (fun v => c * A v) (fun v => d * B v) = (starRingEnd ℂ) c * d * ip A B := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul]
  ring

/-! ## The main theorem -/

lemma ip_applyOp_expand (k l : Idx) (M N : Bool → Bool → ℂ) (φ χ : Bits → ℂ) :
    ip (applyOp k M φ) (applyOp l N χ)
      = ∑ p : Bool × Bool, ∑ q : Bool × Bool,
          (starRingEnd ℂ) (coefM M p) * coefM N q
            * ip (pauli (sel p.1 k) (sel p.2 k) φ) (pauli (sel q.1 l) (sel q.2 l) χ) := by
  have hφ : applyOp k M φ = fun v => ∑ p : Bool × Bool, coefM M p * pauli (sel p.1 k) (sel p.2 k) φ v :=
    funext (applyOp_eq k M φ)
  have hχ : applyOp l N χ = fun v => ∑ q : Bool × Bool, coefM N q * pauli (sel q.1 l) (sel q.2 l) χ v :=
    funext (applyOp_eq l N χ)
  rw [hφ, hχ, ip_sum_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  exact ip_smul_smul _ _ _ _

/-- **The nine-qubit Shor code corrects an arbitrary single-qubit error.**

The two logical states `psi false`, `psi true` are orthonormal, and the Knill–Laflamme
error-correction conditions hold for the set of all errors acting on a single (arbitrary,
unknown) qubit: for any two qubits `k`, `l` and any two single-qubit operators `M`, `N`
there is a constant `w` with `⟨ ψ_a | M_k^† N_l | ψ_b ⟩ = w δ_{ab}`.  Since the Knill–Laflamme
conditions are necessary and sufficient for the existence of a recovery operation, this says
exactly that the code corrects an arbitrary error on one qubit. -/
theorem shor_code_corrects :
    (∀ a b : Bool, ip (psi a) (psi b) = if a = b then 1 else 0) ∧
      ∀ (k l : Idx) (M N : Bool → Bool → ℂ), ∃ w : ℂ, ∀ a b : Bool,
        ip (applyOp k M (psi a)) (applyOp l N (psi b)) = if a = b then w else 0 := by
  refine ⟨ip_psi, ?_⟩
  intro k l M N
  refine ⟨ip (applyOp k M (psi false)) (applyOp l N (psi false)), ?_⟩
  intro a b
  by_cases hab : a = b
  · subst hab
    cases a
    · rfl
    · rw [ip_applyOp_expand, ip_applyOp_expand]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [(pauli_ip_core (sel_support p.1 k) (sel_support p.2 k) (sel_support q.1 l)
        (sel_support q.2 l)).2]
  · simp only [if_neg hab]
    rw [ip_applyOp_expand]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    rw [(pauli_ip_core (sel_support p.1 k) (sel_support p.2 k) (sel_support q.1 l)
      (sel_support q.2 l)).1 a b hab, mul_zero]

/-! ## Sanity checks on the model of single-qubit operators -/

/-- The identity matrix acts as the identity operator. -/
lemma applyOp_id (k : Idx) (ψ : Bits → ℂ) :
    applyOp k (fun s t => if s = t then 1 else 0) ψ = ψ := by
  funext v
  unfold applyOp
  simp [Function.update_eq_self]

/-- The Pauli `X` matrix acts by flipping the `k`-th bit. -/
lemma applyOp_X (k : Idx) (ψ : Bits → ℂ) :
    applyOp k (fun s t => if s = t then 0 else 1) ψ = fun v => ψ (bxor v (bone k)) := by
  funext v
  unfold applyOp
  have h := update_bxor k v
  cases hv : v k <;> rw [hv] at h <;> simp <;> rw [← h] <;> simp

/-! ## A consequence: a single-qubit error preserves the geometry of the code space -/

/-- A general state of the logical qubit, with amplitudes `co false`, `co true`. -/
noncomputable def codeState (co : Bool → ℂ) : Bits → ℂ := fun v => ∑ s : Bool, co s * psi s v

lemma applyOp_sum {ι : Type} [Fintype ι] (k : Idx) (M : Bool → Bool → ℂ) (co : ι → ℂ)
    (F : ι → Bits → ℂ) :
    applyOp k M (fun v => ∑ i, co i * F i v) = fun v => ∑ i, co i * applyOp k M (F i) v := by
  funext v
  unfold applyOp
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- For an arbitrary error `M` on an arbitrary single qubit `k`, all inner products between
code states are scaled by one and the same constant `w`.  In particular no information about
the encoded state leaks into the environment, and the error is correctable. -/
theorem shor_error_scales_inner (k : Idx) (M : Bool → Bool → ℂ) :
    ∃ w : ℂ, ∀ co co' : Bool → ℂ,
      ip (applyOp k M (codeState co)) (applyOp k M (codeState co'))
        = w * ip (codeState co) (codeState co') := by
  obtain ⟨w, hw⟩ := shor_code_corrects.2 k k M M
  refine ⟨w, fun co co' => ?_⟩
  have hA : ∀ c : Bool → ℂ,
      applyOp k M (codeState c) = fun v => ∑ s : Bool, c s * applyOp k M (psi s) v := by
    intro c
    exact applyOp_sum k M c psi
  rw [hA, hA]
  rw [ip_sum_sum (fun s => fun v => co s * applyOp k M (psi s) v)
    (fun t => fun v => co' t * applyOp k M (psi t) v)]
  unfold codeState
  rw [ip_sum_sum (fun s => fun v => co s * psi s v) (fun t => fun v => co' t * psi t v)]
  simp only [ip_smul_smul, hw, ip_psi]
  simp
  ring

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

