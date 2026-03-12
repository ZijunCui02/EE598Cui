/-
  Formalizing Spatial Audio DSP Foundations in Lean 4
  ===================================================
  EE598 Automated Mathematics — Final Project
  Zijun Cui, Winter 2026

  This file formalizes the mathematical foundations of binaural and
  spatial audio processing:

  Part I   — Discrete Convolution: definition, δ-identity, commutativity, linearity
  Part II  — Interaural Time Difference (ITD): Woodworth model, symmetry, monotonicity
  Part III — Ambisonics Rotation: z-axis rotation matrix, orthogonality, det=1, composition
-/

import Mathlib

open scoped Matrix
open Finset

namespace SpatialAudio

-- ============================================================================
-- Part I: Discrete Convolution
-- ============================================================================

/-
  We model finite discrete-time signals as functions Fin N → ℝ.
  At 48 kHz sample rate, a 10-second clip is Fin 480000 → ℝ.

  Subtraction on Fin N (with NeZero N) is modular, giving circular
  convolution — the time-domain equivalent of pointwise DFT multiplication.
  Fin N has AddCommGroup when NeZero N, enabling clean reindexing proofs.
-/

variable {N : ℕ} [NeZero N]

/-- A discrete-time signal of length N. -/
abbrev Signal (N : ℕ) := Fin N → ℝ

/-- The Kronecker delta signal: 1 at index 0, 0 elsewhere. -/
noncomputable def delta : Signal N :=
  fun k => if k = 0 then 1 else 0

/-- Discrete circular convolution:
    (f ⋆ g)[n] = Σ_{k=0}^{N-1} f[k] · g[n - k]  -/
noncomputable def conv (f g : Signal N) : Signal N :=
  fun n => ∑ k : Fin N, f k * g (n - k)

-- ---------------------------------------------------------------------------
-- Theorem: Delta identity — convolving with δ returns the original signal
-- (f ⋆ δ)[n] = f[n]
-- ---------------------------------------------------------------------------

theorem conv_delta (f : Signal N) : conv f delta = f := by
  ext n
  simp only [conv, delta]
  -- Rewrite: if (n - k = 0) ↔ if (k = n), using sub_eq_zero in AddCommGroup
  have : ∀ k : Fin N, f k * (if n - k = 0 then (1 : ℝ) else 0) =
      if k = n then f n else 0 := by
    intro k
    by_cases h : k = n
    · subst h; simp
    · have : n - k ≠ 0 := by rwa [sub_ne_zero, ne_comm]
      simp [h, this]
  simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

-- ---------------------------------------------------------------------------
-- Theorem: Convolution commutativity — conv f g = conv g f
-- Uses reindexing k ↦ n - k via Equiv.subLeft (requires AddCommGroup)
-- ---------------------------------------------------------------------------

theorem conv_comm (f g : Signal N) : conv f g = conv g f := by
  ext n
  simp only [conv]
  exact Fintype.sum_equiv (Equiv.subLeft n) _ _ (fun k => by
    simp [Equiv.subLeft_apply, mul_comm])

-- ---------------------------------------------------------------------------
-- Theorem: Convolution distributes over addition
-- f ⋆ (g + h) = f ⋆ g + f ⋆ h
-- ---------------------------------------------------------------------------

omit [NeZero N] in
theorem conv_add (f g h : Signal N) : conv f (g + h) = conv f g + conv f h := by
  ext n
  simp only [conv, Pi.add_apply, mul_add, Finset.sum_add_distrib]

-- ---------------------------------------------------------------------------
-- Theorem: Convolution respects scalar multiplication
-- f ⋆ (a • g) = a • (f ⋆ g)
-- ---------------------------------------------------------------------------

omit [NeZero N] in
theorem conv_smul (f g : Signal N) (a : ℝ) : conv f (a • g) = a • conv f g := by
  ext n
  simp only [conv, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ k : Fin N, f k * (a * g (n - k))) = a * ∑ k : Fin N, f k * g (n - k) from by
    rw [Finset.mul_sum]; congr 1; ext k; ring]

-- ============================================================================
-- Part II: Interaural Time Difference (ITD) — Woodworth Spherical Head Model
-- ============================================================================

section ITD

/-
  The Woodworth (1938) model approximates the human head as a sphere of
  radius r. For a sound source at azimuth angle θ in the horizontal plane:

      ITD(θ) = (r / c) · (θ + sin θ)

  The two terms capture:
  - r·sin(θ)/c : straight-line path difference (projection of head diameter)
  - r·θ/c : extra "creeping wave" path around the head's curved surface

  Typical values: r ≈ 0.0875 m, c ≈ 343 m/s, giving max ITD ≈ 0.66 ms.
-/

/-- Woodworth interaural time difference model.
    r = head radius, c = speed of sound, θ = azimuth angle. -/
noncomputable def ITD (r c θ : ℝ) : ℝ := (r / c) * (θ + Real.sin θ)

-- ---------------------------------------------------------------------------
-- Theorem: ITD(0) = 0 — no delay when source is straight ahead
-- ---------------------------------------------------------------------------

theorem ITD_zero (r c : ℝ) : ITD r c 0 = 0 := by
  simp [ITD, Real.sin_zero]

-- ---------------------------------------------------------------------------
-- Theorem: ITD(-θ) = -ITD(θ) — left-right symmetry
-- ---------------------------------------------------------------------------

theorem ITD_neg (r c θ : ℝ) : ITD r c (-θ) = -ITD r c θ := by
  unfold ITD; rw [Real.sin_neg]; ring

-- ---------------------------------------------------------------------------
-- Theorem: The derivative of ITD w.r.t. θ is (r/c)(1 + cos θ)
-- ---------------------------------------------------------------------------

theorem hasDerivAt_ITD (r c θ : ℝ) :
    HasDerivAt (ITD r c) ((r / c) * (1 + Real.cos θ)) θ := by
  unfold ITD
  exact ((hasDerivAt_id θ).add (Real.hasDerivAt_sin θ)).const_mul (r / c)

-- ---------------------------------------------------------------------------
-- Theorem: ITD is monotonically increasing on [0, π/2]
-- The derivative (r/c)(1 + cos θ) ≥ 0 since cos θ ≥ 0 on [0, π/2].
-- ---------------------------------------------------------------------------

theorem ITD_monotoneOn (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    MonotoneOn (ITD r c) (Set.Icc 0 (Real.pi / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.pi / 2))
  · -- Continuity on Icc
    exact (continuous_const.mul (continuous_id.add Real.continuous_sin)).continuousOn
  · -- Differentiable on interior
    intro θ _
    exact (hasDerivAt_ITD r c θ).differentiableAt.differentiableWithinAt
  · -- Derivative ≥ 0 on interior
    intro θ hθ
    rw [interior_Icc] at hθ
    rw [(hasDerivAt_ITD r c θ).deriv]
    apply mul_nonneg
    · exact div_nonneg hr.le hc.le
    · have hcos : Real.cos θ ≥ 0 :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
      linarith

end ITD

-- ============================================================================
-- Part III: First-Order Ambisonics — Z-Axis Rotation Matrix
-- ============================================================================

section Rotation

/-
  In first-order Ambisonics (FOA), the horizontal sound field is encoded
  into 3 channels (W, X, Y) via spherical harmonic decomposition.

  Rotating the sound field by angle α around the vertical (z) axis is:

      ┌ W' ┐   ┌ 1     0       0    ┐ ┌ W ┐
      │ X' │ = │ 0   cos α  -sin α  │ │ X │
      └ Y' ┘   └ 0   sin α   cos α  ┘ └ Y ┘

  The W (omnidirectional/pressure) channel is invariant under rotation.
  The X, Y (figure-8/velocity) channels undergo standard 2D rotation.

  Binaural rendering: each channel is convolved with its corresponding
  spherical-harmonic HRTF, then summed to produce left/right ear signals.
-/

/-- Z-axis rotation matrix for first-order Ambisonics (3×3). -/
noncomputable def rotZ (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0;
     0, Real.cos α, -(Real.sin α);
     0, Real.sin α, Real.cos α]

-- ---------------------------------------------------------------------------
-- Theorem: Orthogonality — R(α)ᵀ · R(α) = I
-- Rotation preserves signal energy (inner products are unchanged).
-- ---------------------------------------------------------------------------

theorem rotZ_orthogonal (α : ℝ) : (rotZ α)ᵀ * (rotZ α) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    nlinarith [Real.sin_sq_add_cos_sq α]

-- ---------------------------------------------------------------------------
-- Theorem: det R(α) = 1 — this is a proper rotation (SO(3), not reflection)
-- ---------------------------------------------------------------------------

theorem rotZ_det (α : ℝ) : Matrix.det (rotZ α) = 1 := by
  rw [Matrix.det_fin_three]
  simp [rotZ]
  nlinarith [Real.sin_sq_add_cos_sq α]

-- ---------------------------------------------------------------------------
-- Theorem: Rotation composition — R(α) · R(β) = R(α + β)
-- Two successive rotations compose by adding angles.
-- Essential for real-time head-tracking in VR/AR spatial audio.
-- ---------------------------------------------------------------------------

theorem rotZ_mul (α β : ℝ) : rotZ α * rotZ β = rotZ (α + β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;>
    ring

end Rotation

end SpatialAudio
