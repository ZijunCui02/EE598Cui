/- Binaural rendering pipeline connecting convolution, ITD, and Ambisonics. -/

import SpatialAudio.Convolution
import SpatialAudio.ITD
import SpatialAudio.Ambisonics

open Finset

namespace SpatialAudio

variable {N : ℕ} [NeZero N]

-- ============================================================================
-- Definitions
-- ============================================================================

/-- First-order Ambisonics signal: three channels W (omni), X, Y (figure-8). -/
@[ext]
structure FOASignal (N : ℕ) where
  W : Signal N
  X : Signal N
  Y : Signal N

/-- HRTF filter set for one ear, one filter per Ambisonics channel. -/
structure HRTFSet (N : ℕ) where
  hW : Signal N
  hX : Signal N
  hY : Signal N

/-- Rotate an FOA signal by angle alpha around the vertical axis.
    W is invariant; X and Y undergo 2D rotation. -/
noncomputable def rotateFOA (α : ℝ) (sig : FOASignal N) : FOASignal N where
  W := sig.W
  X := fun n => Real.cos α * sig.X n - Real.sin α * sig.Y n
  Y := fun n => Real.sin α * sig.X n + Real.cos α * sig.Y n

/-- Binaural rendering for one ear: convolve each FOA channel with its
    corresponding HRTF filter and sum the results. -/
noncomputable def renderEar (sig : FOASignal N) (hrtf : HRTFSet N) : Signal N :=
  fun n => conv sig.W hrtf.hW n + conv sig.X hrtf.hX n + conv sig.Y hrtf.hY n

-- ============================================================================
-- Theorems
-- ============================================================================

-- Zero rotation is the identity on FOA signals.
omit [NeZero N] in
theorem rotateFOA_zero (sig : FOASignal N) : rotateFOA 0 sig = sig := by
  ext n <;> simp [rotateFOA, Real.cos_zero, Real.sin_zero]

-- Composing two rotations adds the angles.
omit [NeZero N] in
theorem rotateFOA_comp (α β : ℝ) (sig : FOASignal N) :
    rotateFOA α (rotateFOA β sig) = rotateFOA (α + β) sig := by
  ext n
  · -- W channel: unchanged by both rotations
    simp [rotateFOA]
  · -- X channel: cos(a)(cos(b)x - sin(b)y) - sin(a)(sin(b)x + cos(b)y) = cos(a+b)x - sin(a+b)y
    simp only [rotateFOA, Real.cos_add, Real.sin_add]
    ring
  · -- Y channel: sin(a)(cos(b)x - sin(b)y) + cos(a)(sin(b)x + cos(b)y) = sin(a+b)x + cos(a+b)y
    simp only [rotateFOA, Real.cos_add, Real.sin_add]
    ring

-- Rendering with zero rotation equals rendering the original signal directly.
omit [NeZero N] in
theorem renderEar_rotateFOA_zero (sig : FOASignal N) (hrtf : HRTFSet N) :
    renderEar (rotateFOA 0 sig) hrtf = renderEar sig hrtf := by
  rw [rotateFOA_zero]

-- ============================================================================
-- Rendering linearity
-- ============================================================================

/-- Pointwise addition of two FOA signals. -/
noncomputable instance : Add (FOASignal N) where
  add a b := ⟨a.W + b.W, a.X + b.X, a.Y + b.Y⟩

-- Rendering is additive: rendering the sum of two signals equals the sum
-- of rendering each signal individually. Uses conv_add from Convolution.
theorem renderEar_add (sig₁ sig₂ : FOASignal N) (hrtf : HRTFSet N) :
    renderEar (sig₁ + sig₂) hrtf = renderEar sig₁ hrtf + renderEar sig₂ hrtf := by
  ext n
  simp only [renderEar, Pi.add_apply,
    show (sig₁ + sig₂).W = sig₁.W + sig₂.W from rfl,
    show (sig₁ + sig₂).X = sig₁.X + sig₂.X from rfl,
    show (sig₁ + sig₂).Y = sig₁.Y + sig₂.Y from rfl,
    add_conv]
  ring

-- ============================================================================
-- Connection to ITD
-- ============================================================================

-- ITD gives interaural delay in seconds. Multiplying by sample rate fs
-- converts to a delay in samples, bridging the continuous ITD model
-- with discrete signal indexing.

/-- ITD expressed in samples at a given sample rate fs. -/
noncomputable def itdSamples (r c fs θ : ℝ) : ℝ := fs * ITD r c θ

-- Sample delay is zero when the source is straight ahead.
theorem itdSamples_zero (r c fs : ℝ) : itdSamples r c fs 0 = 0 := by
  simp [itdSamples, ITD_zero]

-- Sample delay has left-right symmetry: itdSamples(-theta) = -itdSamples(theta).
theorem itdSamples_neg (r c fs θ : ℝ) : itdSamples r c fs (-θ) = -itdSamples r c fs θ := by
  simp [itdSamples, ITD_neg, mul_neg]

end SpatialAudio
