/- First-order Ambisonics z-axis rotation and its group structure. -/

import Mathlib

open scoped Matrix

namespace SpatialAudio

section Rotation

/-
  First-order Ambisonics (FOA) encodes the horizontal sound field into
  3 channels (W, X, Y) via spherical harmonics.

  Rotating the field by angle alpha around the z-axis:

      [ W' ]   [ 1     0       0    ] [ W ]
      [ X' ] = [ 0   cos a  -sin a  ] [ X ]
      [ Y' ]   [ 0   sin a   cos a  ] [ Y ]

  W (omnidirectional) is invariant. X, Y undergo standard 2D rotation.
-/

-- ============================================================================
-- Definition
-- ============================================================================

/-- Z-axis rotation matrix for first-order Ambisonics (3x3). -/
noncomputable def rotZ (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0;
     0, Real.cos α, -(Real.sin α);
     0, Real.sin α, Real.cos α]

-- ============================================================================
-- Basic properties
-- ============================================================================

-- R(alpha)^T * R(alpha) = I: rotation preserves inner products (energy).
theorem rotZ_orthogonal (α : ℝ) : (rotZ α)ᵀ * (rotZ α) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    nlinarith [Real.sin_sq_add_cos_sq α]

-- det R(alpha) = 1: proper rotation, not a reflection.
theorem rotZ_det (α : ℝ) : Matrix.det (rotZ α) = 1 := by
  rw [Matrix.det_fin_three]
  simp [rotZ]
  nlinarith [Real.sin_sq_add_cos_sq α]

-- R(alpha) * R(beta) = R(alpha + beta): rotation composition.
theorem rotZ_mul (α β : ℝ) : rotZ α * rotZ β = rotZ (α + β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;>
    ring

-- ============================================================================
-- Group structure
-- ============================================================================

-- R(0) = I: zero rotation is the identity matrix.
theorem rotZ_zero : rotZ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZ]

-- R(alpha) * R(-alpha) = I: every rotation has an inverse.
theorem rotZ_neg (α : ℝ) : rotZ α * rotZ (-α) = 1 := by
  rw [rotZ_mul, add_neg_cancel, rotZ_zero]

-- The map alpha -> rotZ(alpha) is a monoid homomorphism from (R, +) to (Mat_3, *).
-- This witnesses that rotZ preserves the group operation:
-- identity maps to identity, and addition maps to matrix multiplication.
noncomputable def rotZHom : Multiplicative ℝ →* Matrix (Fin 3) (Fin 3) ℝ where
  toFun α := rotZ (Multiplicative.toAdd α)
  map_one' := by simp [toAdd_one, rotZ_zero]
  map_mul' x y := by
    simp only [toAdd_mul]
    exact (rotZ_mul _ _).symm

end Rotation

end SpatialAudio
