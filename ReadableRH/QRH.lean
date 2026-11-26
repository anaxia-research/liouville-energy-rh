import ReadableRH.Main
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Every half-plane `Re s > θ` with `θ ≥ 1/2` is free of zeros

This is Corollary `cor:qrh` of the paper (the quasi-Riemann hypothesis in its strongest
form). From Mathlib's `RiemannHypothesis`, the Riemann zeta function has no zero in any
half-plane `Re s > θ` with `θ ≥ 1/2`. From `HypothesisH` the same holds for every Dirichlet
`L`-function, and the window bound gives both.
-/

open Complex DirichletCharacter

namespace ReadableRH

/-- The Riemann hypothesis gives every zero-free half-plane `Re s > θ`, `θ ≥ 1/2`. -/
theorem zeta_ne_zero_of_RH (hRH : RiemannHypothesis) {θ : ℝ} (hθ : 1 / 2 ≤ θ) (s : ℂ)
    (hs : θ < s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero hz
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have hre : (-2 * ((n : ℂ) + 1)).re = -(2 * ((n : ℝ) + 1)) := by
      simp [Complex.mul_re]
    rw [hre] at hs
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := hRH s hz htriv hs1
  linarith

/-- Hypothesis H gives every zero-free half-plane `Re s > θ`, `θ ≥ 1/2`, for every Dirichlet
`L`-function. -/
theorem LFunction_ne_zero_of_H (h : HypothesisH) {θ : ℝ} (hθ : 1 / 2 ≤ θ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : θ < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ s ≠ 0 :=
  h N χ s (by linarith) hχs

/-- The window bound gives every zero-free half-plane `Re s > θ`, `θ ≥ 1/2`, for `ζ`. -/
theorem zeta_ne_zero_of_windowBound (hW : WindowBound) {θ : ℝ} (hθ : 1 / 2 ≤ θ) (s : ℂ)
    (hs : θ < s.re) : riemannZeta s ≠ 0 :=
  zeta_ne_zero_of_RH (riemannHypothesis_of_windowBound hW) hθ s hs

end ReadableRH
