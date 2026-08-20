# Quantum-computing autonomous Aristotle loop — 8h / 16 batches

**Goal (user, 2026-08-04 night):** wake up to **≥56 verified quantum-computing proofs**. Run every
~30 min for 8h (**16 batches**); each batch author+submit **7** TRUE, self-contained, Mathlib-vetted
QC targets to Aristotle, AND harvest/independently AXLE-verify @lean-4.32.0 whatever has landed.

## Discipline (non-negotiable)
- Only **TRUE** statements I'm confident of; never submit a false/guessed identity. Aristotle proves
  true theorems only; a wrong matrix/phase = wasted refutation.
- Bare `import Mathlib`; no non-core/Archive namespaces; no invented lemmas.
- Toolchain in each target dir: `leanprover/lean4:v4.28.0`. Verify returns at **AXLE @4.32**.
- Watch the 4.28→4.32 drift (strip any local re-def Mathlib now ships, e.g. `liouville`).
- Honest framing: formalizing **known** QC algebra with Brockian (pentagon/√5/φ/five) structure —
  NOT new physics, NOT new algorithms.

## Per-batch procedure (each wake)
1. `python3 aristotle/qc_harvest.py`  → downloads any landed sent-projects, AXLE-checks @4.32,
   appends verdicts to `aristotle/qc_verified.log`, prints cumulative tally.
2. Author the next family's **7** targets (see roadmap), each `aristotle/<slug>/{lean-toolchain,<Name>.lean}`
   with a `sorry`; submit via `uvx --from aristotlelib@latest aristotle submit "<prompt>" --project-dir …`;
   append each `<projid> <slug>` to `aristotle/qc_projects.txt`.
3. Update the batch counter below; if batch < 16 → `ScheduleWakeup(1800s)`; else stop + final summary.

## State
- **Batch counter: 16** (ALL 16 batches sent; 14,15,16 sent early per user; 103 verified so far, 14-16 proving)
  qft-unitary, braid-tl, stabilizer → ~13 theorems in flight).
- Sent-projects ledger: `aristotle/qc_projects.txt`. Verdicts: `aristotle/qc_verified.log`.

## 16-family roadmap (author 7 each; all concrete/known-true, Brockian five woven through)
1. **Single-qubit Pauli algebra** — X²=Y²=Z²=1; XY=iZ, YZ=iX, ZX=iY; XYZ=iI.
2. **Hadamard & basis change** — H²=1; H unitary; HXH=Z; HZH=X; HYH=−Y; det H=−1; H=(X+Z)/√2.
3. **Phase gates** — S=diag(1,i), S²=Z, S⁴=1; T=diag(1,e^{iπ/4}), T²=S, T⁸=1; SXS⁻¹=Y.
4. **Two-qubit gates** — CNOT²=1, CNOT unitary; CZ²=1; SWAP²=1; SWAP unitary; CZ symmetric; CNOT is a permutation matrix.
5. **Bell states** — 4 Bell states unit-norm; Bell⁺ is +1-eigenvector of X⊗X and of Z⊗Z; Bell basis orthonormal.
6. **GHZ / W states** — GHZ unit-norm; stabilized by X⊗X⊗X; by Z⊗Z⊗I; W-state norm; orthogonality.
7. **Fifth roots of unity (Brockian)** — ω=e^{2πi/5}: ω⁵=1; ∑₀⁴ ωᵏ=0; 2cos(2π/5)=1/φ=φ−1; 2cos(4π/5)=−φ; product of (x−ωᵏ)=xⁿ−1.
8. **QFT family** — QFT₂=H; QFT(d) unitary; QFT⁴=1; QFT⁻¹; QFT diagonalizes the cyclic shift (F·X=Z·F).
9. **Qudit Weyl/Heisenberg** — X^d=1, Z^d=1; tr X=0, tr Z=0; W(a,b)=X^a Z^b group law; (XZ)^d phase; shift/clock unitary.
10. **Density matrices / purity** — |ψ⟩⟨ψ| idempotent; trace 1; Hermitian; Pauli traceless; tr(σᵢσⱼ)=2δᵢⱼ.
11. **Fibonacci-anyon extras** — F orthogonal/symmetric; quantum dim d=φ (d²=d+1); pentagon-lite; R-eigenvalues are roots of unity; τ-fusion Perron root.
12. **Cyclotomic / Gauss (Brockian five)** — quadratic Gauss sum mod 5; |g|²=5; cos(π/5)=φ/2; √5 = 1+2·(golden combo); Φ₅ irreducible/eval.
13. **Clifford relations** — (HS)³ = phase·I; H,S orders; S H S; Clifford permutes Paulis.
14. **3-qubit gates** — Toffoli²=1, Toffoli unitary/permutation; Fredkin²=1; Toffoli = controlled-CNOT.
15. **Rotations / SU(2)** — exp(iθZ)=cosθ·I+isinθ·Z; Rx(π)=−iX; Rz unitary; Pauli exponential; Euler-angle product (pick provable subset).
16. **Projectors / measurement** — |0⟩⟨0|+|1⟩⟨1|=1; projectors idempotent+Hermitian; orthogonal; qudit completeness ∑|k⟩⟨k|=1.

Prefer concrete small matrices (2×2/4×4) — highest Aristotle success. 112 targets → ≥56 verified is the bar.
