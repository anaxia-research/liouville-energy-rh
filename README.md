# liouville-energy-rh

Lean 4 formalization accompanying the paper

> **Proof of the Riemann and Generalized Riemann Hypotheses**
> Deep Bhattacharjee and Ushashi Bhattacharya, 2026.
> Preprints.org 202606.1350, version 5.

**Corresponding author:** Deep Bhattacharjee
(itsdeep@live.com, d.bhattacharjee@erl-forschung.de;
ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)).
Code contact: egspl@proton.me, GitHub [creelie](https://github.com/creelie).

---

## Overview

The paper shows that the Riemann hypothesis (RH) and its generalization to
Dirichlet L-functions (GRH) are each equivalent to one energy bound for the
Liouville function on a sparse sequence of windows. It then proves both from a
single cited window theorem.

This repository checks every step of that deduction in Lean 4. It is written to
be read beside the paper. Every theorem listed below builds with no `sorry` and
depends only on the three standard axioms `propext`, `Classical.choice` and
`Quot.sound`. The output of `#print axioms` is recorded in
[`axioms.txt`](axioms.txt) and [`corollaries/axioms.txt`](corollaries/axioms.txt).

## Main results

| Result in the paper | Lean theorem | Statement |
|---|---|---|
| Windowed energy principle | `ReadableRH.windowed_energy_principle` | A family energy bounded by C y^θ on windows [Y, Y^{1+δ}] at arbitrarily large heights makes every member zero-free in Re s > θ. |
| RH from the window theorem | `ReadableRH.riemannHypothesis_of_windowBound` | The window bound implies Mathlib's `RiemannHypothesis`. |
| GRH from the window theorem | `ReadableRH.grh_of_windowBound` | The window bound puts every zero of a primitive Dirichlet L-function in the critical strip on Re s = 1/2. |
| Functional-equation step | `ReadableRH.rh_of_H`, `ReadableRH.critLine` | The zero-free half-plane Re s > 1/2 gives RH and GRH. |
| Log-derivative criterion | `ReadableRH.hypothesisH_of_logDeriv`, `ReadableRH.riemannHypothesis_of_logDeriv`, `ReadableRH.grh_of_logDeriv` | If every L'/L(s, χ) is holomorphic on Re s > 1/2, s ≠ 1, then the half-plane, RH and GRH follow. |
| Host decomposition | `UpperTheory.Comparison₂.core_gm` | The core energy bound of the host decomposition. |
| Discarded characters | `UpperTheory.Comparison₂.sigA_le` | The discarded part is at most 4o · x^{1/2+ε}. |
| Kept characters | `Deduction.ch_core` | The kept part is bounded by the host energy and the discarded part. |

## The cited input

The window bound (`WindowBound` in [`ReadableRH/Main.lean`](ReadableRH/Main.lean))
is the one hypothesis of the top-level theorems. It is the window theorem of
L. Alpöge (alpo.ge, November 2026), which rests on the Galois representations
attached to polarized cuspidal automorphic representations over CM fields
(Harris–Taylor, Shin, Chenevier–Harris, Harris–Lan–Taylor–Thorne, Scholze,
Caraiani). Mathlib has no automorphic forms, so the paper cites this step and
it is not formalized here. The host decomposition, which is one of its steps,
is checked in [`ReadableRH/Host/`](ReadableRH/Host).

## Building

Requirements: [elan](https://github.com/leanprover/elan). The toolchain and
the Mathlib revision are pinned.

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

Lean 4.33.1, Mathlib `0df444a`. With Mathlib's prebuilt cache, the build takes
about 9 minutes on a four-core machine, after a cache download of about 3 minutes.

The corollaries are a separate project on Lean 4.34.1:

```
cd corollaries
lake exe cache get
lake build
lake env lean Axioms.lean
```

This takes about 6 minutes on the same machine, after a cache download of about
3 minutes.

## Corollaries

Each corollary takes the zero-free half-plane (Hypothesis H,
`LiouvilleEnergyRH.HypothesisH`) as an explicit argument.

| Lean theorem | Statement |
|---|---|
| `lindelof_bound`, `lindelof_half` | Lindelöf bounds for Dirichlet L-functions |
| `polya_vinogradov`, `character_sum_bound`, `character_sum_bound_half`, `character_sum_le_rpow`, `vinogradov_character_sum` | Character-sum bounds |
| `prime_sum_bound` | Twisted prime sums |
| `least_nonresidue`, `least_prime_primitive_root`, `erdos_985` | Least non-residues and primitive roots |
| `logDeriv_one_bound`, `euler_kronecker_bound` | Logarithmic derivatives at s = 1 and Euler–Kronecker constants |

## Repository layout

```
ReadableRH/
  Window/               windowed energy principle (Landau-type theorem)
  Host/                 host decomposition
  FunctionalEquation.lean
  LogDeriv.lean         log-derivative criterion
  Main.lean             window bound ⇒ RH and GRH
Axioms.lean             #print axioms for the theorems above
corollaries/            consequences of the zero-free half-plane (Lean 4.34.1)
  LiouvilleEnergyRH/    Lindelöf, character sums, prime sums, least non-residue,
                        least prime primitive root, Erdős 985, Euler–Kronecker
  Vinogradov/           Pólya–Vinogradov and Vinogradov's character-sum conjectures
```

## Citation

```bibtex
@misc{BhattacharjeeBhattacharya2026,
  author       = {Bhattacharjee, Deep and Bhattacharya, Ushashi},
  title        = {Proof of the Riemann and Generalized Riemann Hypotheses},
  year         = {2026},
  howpublished = {Preprints.org, 202606.1350, version 5},
  note         = {Lean formalization: https://github.com/anaxia-research/liouville-energy-rh}
}
```

## Credits and licence

`ReadableRH/Window/` and `ReadableRH/Host/` are taken from L. Alpöge's Lean
project, with only the import lines changed. See [`NOTICE`](NOTICE) for these
and the other third-party files. Our own files are under the MIT licence
([`LICENSE`](LICENSE)). The Vinogradov files are under Apache 2.0
([`corollaries/LICENSE-APACHE`](corollaries/LICENSE-APACHE)).
