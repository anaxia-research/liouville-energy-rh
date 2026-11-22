import ReadableRH.FunctionalEquation
import ReadableRH.Window.ZeroFreeOfRpowWindow

/-!
# The Riemann hypothesis and GRH from a windowed energy bound

This is the top of the proof, written to be read.

* `Deduction.CharFamily` is a finite weighted family of Dirichlet characters, and
  `Deduction.Gm F y` its energy `E_F(y) = Σ aᵢ Re Gχᵢ(y)`, built from the von Mangoldt
  sums `Σ_{n≤y} Λ(n) χ(n) (y/n - 1)` minus their main terms.
* `WindowBound` says: every primitive character sits in some family whose energy is at
  most `C y^{1/2+ε}` on windows `[Y, Y^{1+δ}]` at arbitrarily large heights.
  Only windows are needed, nothing between them.
* `windowed_energy_principle` (files in `ReadableRH/Window`, a Landau-type theorem read off
  the Taylor coefficients of the Mellin transform of the energy) turns that into a
  zero-free half-plane.
* `FunctionalEquation` turns the half-plane into RH and GRH on the critical line.

`WindowBound` is the one input. In L. Alpöge's construction (alpo.ge, November 2026) it is
proved from the Galois representations attached to regular algebraic polarized cuspidal
automorphic representations of `GL_n` over CM fields (Harris–Taylor, Shin, Chenevier–Harris,
Harris–Lan–Taylor–Thorne, Scholze, Caraiani) and his bound for the lengths of
Tate–Shafarevich groups along cyclotomic towers. Those theorems are not in Mathlib, so
`WindowBound` stays an explicit hypothesis here. The windowed principle and the
functional-equation step are adapted from his project.
-/

open Complex DirichletCharacter Deduction

namespace ReadableRH

/-- A character is admissible if it is the character mod `1` or non-trivial. -/
def Admissible {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop := N = 1 ∨ χ ≠ 1

/-- **The windowed energy bound.** -/
def WindowBound : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (F : CharFamily) (i : F.ι) (δ C : ℝ), 0 < δ ∧
        (∀ s, LFunction (F.χ i) s = LFunction χ s) ∧
        ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
          ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ ((1 : ℝ) / 2 + ε)

/-- **Windowed energy principle.** An energy bound `C y^θ` on windows at arbitrarily large
heights forces every member of the family to be zero-free in `Re s > θ`. -/
theorem windowed_energy_principle (F : CharFamily) {θ δ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
    ∀ i, ∀ s : ℂ, θ < s.re → LFunction (F.χ i) s ≠ 0 :=
  zeroFree_of_rpow_window F hθ hθ1 hδ h

/-- The window bound makes every primitive `L`-function zero-free in `Re s > 1/2`. -/
theorem admissible_zeroFree (hW : WindowBound) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (s : ℂ) (hs : 1 / 2 < s.re) : LFunction χ s ≠ 0 := by
  set ε : ℝ := min ((s.re - 1 / 2) / 2) (1 / 4) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεs : 1 / 2 + ε < s.re := by
    have : ε ≤ (s.re - 1 / 2) / 2 := min_le_left _ _
    linarith
  obtain ⟨F, i, δ, C, hδ, hL, h⟩ := hW N χ hχ ε hε0 hε1
  rw [← hL]
  exact windowed_energy_principle F (by linarith) (by linarith) hδ h i s hεs

/-- **The Riemann hypothesis**, from the window bound. -/
theorem riemannHypothesis_of_windowBound (hW : WindowBound) : RiemannHypothesis :=
  rh_of_right fun s hs _ => by
    have hp : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
      rw [isPrimitive_def, conductor_one]
    have := admissible_zeroFree hW 1 (1 : DirichletCharacter ℂ 1) hp s hs
    rwa [LFunction_modOne_eq] at this

/-- A primitive character is admissible: the trivial character has conductor `1`. -/
theorem admissible_of_primitive {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) : Admissible χ := by
  by_cases h : χ = 1
  · left
    have := hχ
    rw [isPrimitive_def, h, conductor_one] at this
    exact this.symm
  · exact Or.inr h

/-- **GRH for primitive Dirichlet `L`-functions**, from the window bound: every zero in the
critical strip lies on `Re s = 1/2`. -/
theorem grh_of_windowBound (hW : WindowBound) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) :
    s.re = 1 / 2 := by
  have hs0 : s ≠ 0 := fun e => by simp [e] at h0
  have hs1 : s ≠ 1 := fun e => by simp [e] at h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : χ⁻¹.IsPrimitive := by
      rw [isPrimitive_def, conductor_inv]; exact hχ
    have hc : completedLFunction χ s = 0 := by
      rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)] at hz
      exact (div_eq_zero_iff.1 hz).resolve_right (gammaFactor_ne_zero χ h0)
    have hfe := hinv.completedLFunction_one_sub s
    rw [inv_inv, hc, mul_zero] at hfe
    have h2 : (1 - s) ≠ 0 := sub_ne_zero.2 hs1.symm
    refine admissible_zeroFree hW N χ⁻¹ hinv (1 - s)
      (by rw [sub_re, one_re]; linarith) ?_
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inl h2), hfe, zero_div]
  · exact admissible_zeroFree hW N χ hχ s hgt hz

end ReadableRH
