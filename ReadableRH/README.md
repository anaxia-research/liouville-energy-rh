# ReadableRH: the top of the proof, in 33 files

A self-contained Lean 4 project (Lean 4.33.1, Mathlib `0df444a`) of about 2,700 lines, with no `sorry` and
only the standard axioms (`axioms.txt`). It is separate from the root project because it pins a different Mathlib.

```
cd ReadableRH && lake exe cache get && lake build && lake env lean Axioms.lean
```

| Theorem | Statement |
|---|---|
| `windowed_energy_principle` | family energy ≤ C y^θ on windows [Y, Y^{1+δ}] at arbitrarily large heights ⇒ every member zero-free in Re s > θ (paper, windowed energy principle) |
| `riemannHypothesis_of_windowBound` | `WindowBound` ⇒ Mathlib's `RiemannHypothesis` |
| `grh_of_windowBound` | `WindowBound` ⇒ zeros of primitive Dirichlet L-functions in the strip lie on Re s = 1/2 |
| `rh_of_H`, `critLine` | Hypothesis H ⇒ RH and GRH |

`WindowBound` (in `ReadableRH/Main.lean`) is the window theorem of the paper, stated as an explicit hypothesis:
it is the one cited input, due to L. Alpöge (alpo.ge, November 2026), and is not formalized here.
The files in `ReadableRH/Window/` and the functional-equation step are adapted from his project.
