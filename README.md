# liouville-energy-rh

Lean 4 formalization for the paper

> D. Bhattacharjee and U. Bhattacharya, *Proof of the Riemann and Generalized Riemann Hypotheses: A Realistic Human-Readable Proof through One Energy Bound*, 2026.

The repository holds Lean files only. Every theorem listed below builds with no `sorry` and depends only on the three standard axioms `propext`, `Classical.choice` and `Quot.sound` (see [`axioms.txt`](axioms.txt) and [`corollaries/axioms.txt`](corollaries/axioms.txt)).

## Build

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

Lean 4.33.1, Mathlib `0df444a`. With Mathlib's prebuilt cache, the build takes about 9 minutes on a four-core machine, after a cache download of about 3 minutes.

The corollaries are a separate project on Lean 4.34.1:

```
cd corollaries
lake exe cache get
lake build
lake env lean Axioms.lean
```

It takes about 6 minutes on the same machine, after a cache download of about 3 minutes.

## What is checked

| Paper | Lean theorem | Statement |
|---|---|---|
| Windowed energy principle | `ReadableRH.windowed_energy_principle` | A family energy bounded by C y^θ on windows [Y, Y^{1+δ}] at arbitrarily large heights makes every member zero-free in Re s > θ. |
| From the window theorem to RH | `ReadableRH.riemannHypothesis_of_windowBound` | The window bound implies Mathlib's `RiemannHypothesis`. |
| From the window theorem to GRH | `ReadableRH.grh_of_windowBound` | The window bound puts every zero of a primitive Dirichlet L-function in the critical strip on Re s = 1/2. |
| Functional-equation step | `ReadableRH.rh_of_H`, `ReadableRH.critLine` | The zero-free half-plane Re s > 1/2 gives RH and GRH. |
| Host decomposition | `UpperTheory.Comparison₂.core_gm` | The core energy bound of the host decomposition. |
| Discarded characters | `UpperTheory.Comparison₂.sigA_le` | The discarded part is at most 4o · x^{1/2+ε}. |
| Kept characters | `Deduction.ch_core` | The kept part is bounded by the host energy and the discarded part. |

## The cited input

The window bound (`WindowBound` in [`ReadableRH/Main.lean`](ReadableRH/Main.lean)) is the one hypothesis of the top-level theorems. It is the window theorem of L. Alpöge (alpo.ge, November 2026), which rests on the Galois representations attached to polarized cuspidal automorphic representations over CM fields (Harris–Taylor, Shin, Chenevier–Harris, Harris–Lan–Taylor–Thorne, Scholze, Caraiani). Mathlib has no automorphic forms, so that step is cited in the paper and is not formalized here. The host decomposition, which is one of its steps, is checked in `ReadableRH/Host/`.

## Layout

```
ReadableRH/
  Window/               windowed energy principle (Landau-type theorem)
  Host/                 host decomposition
  FunctionalEquation.lean
  Main.lean             window bound ⇒ RH and GRH
Axioms.lean             #print axioms for the theorems above
corollaries/            consequences of the zero-free half-plane (Lean 4.34.1)
  LiouvilleEnergyRH/    Lindelöf, character sums, prime sums, least non-residue,
                        least prime primitive root, Erdős 985, Euler–Kronecker
  Vinogradov/           Pólya–Vinogradov and Vinogradov's character-sum conjectures
```

## Corollaries

Each takes the zero-free half-plane (Hypothesis H, `LiouvilleEnergyRH.HypothesisH`) as an explicit argument.

| Lean theorem | Statement |
|---|---|
| `lindelof_bound`, `lindelof_half` | Lindelöf bounds for Dirichlet L-functions |
| `polya_vinogradov`, `character_sum_bound`, `character_sum_bound_half`, `character_sum_le_rpow`, `vinogradov_character_sum` | character-sum bounds |
| `prime_sum_bound` | twisted prime sums |
| `least_nonresidue`, `least_prime_primitive_root`, `erdos_985` | least non-residues and primitive roots |
| `logDeriv_one_bound`, `euler_kronecker_bound` | logarithmic derivatives at s = 1 and Euler–Kronecker constants |

## Credits and licence

`ReadableRH/Window/` and `ReadableRH/Host/` are taken from L. Alpöge's Lean project with only import lines changed; see [`NOTICE`](NOTICE) for these and the other third-party files. Our own files are under the MIT licence ([`LICENSE`](LICENSE)); the Vinogradov files are under Apache 2.0 ([`corollaries/LICENSE-APACHE`](corollaries/LICENSE-APACHE)).
