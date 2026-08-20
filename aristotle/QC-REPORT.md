# Verified quantum-computing theorems — FINAL report (2026-08-05)

**21 projects · 124 theorem-level declarations · all independently AXLE-verified @lean-4.32.0, axiom-clean.**
16-batch autonomous loop complete: all 5 seed projects + 16 batches VERIFIED — **zero failures, zero re-queues**.
Aristotle-generated @4.28, re-verified on our kernel @4.32 (dep only on {propext, Classical.choice, Quot.sound}).

## Thematic breakdown

| Theme | Theorems |
|---|---:|
| Single-qubit gate algebra (Pauli, Hadamard, phase) | 21 |
| Entanglement & stabilizers (stabilizer, Bell, GHZ/W) | 19 |
| Brockian-five number theory (fifth roots, cyclotomic-5) | 14 |
| Topological QC / Fibonacci anyons (F-move, braid, TL) | 11 |
| Qudit generalized Pauli (Weyl-Heisenberg) | 9 |
| Quantum Fourier transform | 8 |
| Two- & three-qubit gates (CNOT/CZ/SWAP, Toffoli/Fredkin/CCZ) | 14 |
| Clifford group conjugations | 7 |
| SU(2) rotations (Rz, spinor 2π/4π) | 7 |
| Density, projectors & measurement | 14 |
| **TOTAL** | **124** |

**Brockian ↔ QC through-line: ~42 theorems** — Fibonacci-anyon quantum dimension φ, qudit-5 Weyl group,
QFT-on-ℤ/5, and fifth-root/cyclotomic-5 number theory: the pentagon/√5/φ spine realized in quantum computing.

## Honest caveats
- Formalizations of **known** QC algebra with Brockian structure — real, machine-checked, first-for-Mathlib
  (no anyon/qudit/Weyl content existed in Mathlib) — but **not new physics or new algorithms**.
- The 124 counts a few helper lemmas Aristotle introduced (e.g. GHZ project = 9, not the 7 authored).
- **Verified + staged, not yet registry-committed** — Codex's Brockian.lean is mid-edit and the repo's
  committed-secrets block a safe push; all 21 modules are ready for a coordinated batch commit.

Per-project verdicts: `aristotle/qc_verified.log` · sent ledger: `aristotle/qc_projects.txt`.

## Registry fold (2026-08-05)
All 21 QC modules folded into the registry: renamed to unique Brockian.<Module> namespaces,
independently AXLE-attested @lean-4.32.0, imported in Brockian.lean, verdicts added, gen_registry x2
+ firewall + manifests PASS. Registry PROVED: 11,002 -> 11,126 (+124 QC theorems).
Working-tree + registry integration only; git push deferred (Codex Brockian.lean dirty + committed-secrets).

## Riemann-lab push (2026-08-05)
Prime Explorer 3D / Riemann Labs (dd8308ac): /quantum frontier page (thematic breakdown + Brockian
through-line + honest scope) + all 21 Lean sources in public/proofs/qc/ + clickable proof-drawers
(source + AXLE certificate per module).
