/- Woodworth spherical head model for interaural time difference. -/

import Mathlib

namespace SpatialAudio

section ITD

/-
  The Woodworth (1938) model approximates the human head as a sphere
  of radius r. For a sound source at azimuth theta:

      ITD(theta) = (r / c) * (theta + sin theta)

  The two terms capture the straight-line path difference (r sin theta / c)
  and the creeping-wave path around the curved surface (r theta / c).
  Typical values: r = 0.0875 m, c = 343 m/s, giving max ITD = 0.66 ms.
-/

/-- Woodworth interaural time difference.
    r = head radius, c = speed of sound, theta = azimuth angle. -/
noncomputable def ITD (r c θ : ℝ) : ℝ := (r / c) * (θ + Real.sin θ)

-- ITD vanishes at zero azimuth (source straight ahead, ears equidistant).
theorem ITD_zero (r c : ℝ) : ITD r c 0 = 0 := by
  simp [ITD, Real.sin_zero]

-- ITD is odd: left-right symmetry of the spherical head.
theorem ITD_neg (r c θ : ℝ) : ITD r c (-θ) = -ITD r c θ := by
  unfold ITD; rw [Real.sin_neg]; ring

-- Derivative of ITD w.r.t. theta is (r/c)(1 + cos theta).
theorem hasDerivAt_ITD (r c θ : ℝ) :
    HasDerivAt (ITD r c) ((r / c) * (1 + Real.cos θ)) θ := by
  unfold ITD
  exact ((hasDerivAt_id θ).add (Real.hasDerivAt_sin θ)).const_mul (r / c)

-- ITD is monotone on [0, pi/2] when r > 0 and c > 0.
-- The derivative (r/c)(1 + cos theta) >= 0 since cos >= 0 on this interval.
theorem ITD_monotoneOn (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    MonotoneOn (ITD r c) (Set.Icc 0 (Real.pi / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.pi / 2))
  · exact (continuous_const.mul (continuous_id.add Real.continuous_sin)).continuousOn
  · intro θ _
    exact (hasDerivAt_ITD r c θ).differentiableAt.differentiableWithinAt
  · intro θ hθ
    rw [interior_Icc] at hθ
    rw [(hasDerivAt_ITD r c θ).deriv]
    apply mul_nonneg
    · exact div_nonneg hr.le hc.le
    · have hcos : Real.cos θ ≥ 0 :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
      linarith

end ITD

end SpatialAudio
