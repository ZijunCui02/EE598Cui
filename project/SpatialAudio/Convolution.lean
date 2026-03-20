/- Discrete circular convolution and its algebraic properties. -/

import Mathlib

open Finset

namespace SpatialAudio

-- ============================================================================
-- Definitions
-- ============================================================================

variable {N : ℕ} [NeZero N]

/-- A discrete-time signal of length N, modeled as Fin N -> R.
    At 48 kHz, a 1-second clip is Fin 48000 -> R. -/
abbrev Signal (N : ℕ) := Fin N → ℝ

/-- Kronecker delta: 1 at index 0, 0 elsewhere. -/
noncomputable def delta : Signal N :=
  fun k => if k = 0 then 1 else 0

/-- Circular convolution: (f * g)[n] = sum_{k} f[k] g[n - k].
    Subtraction on Fin N is modular (AddCommGroup), giving circular convolution. -/
noncomputable def conv (f g : Signal N) : Signal N :=
  fun n => ∑ k : Fin N, f k * g (n - k)

-- ============================================================================
-- Theorems
-- ============================================================================

-- Convolving with delta returns the original signal: conv f delta = f.
theorem conv_delta (f : Signal N) : conv f delta = f := by
  ext n
  simp only [conv, delta]
  have : ∀ k : Fin N, f k * (if n - k = 0 then (1 : ℝ) else 0) =
      if k = n then f n else 0 := by
    intro k
    by_cases h : k = n
    · subst h; simp
    · have : n - k ≠ 0 := by rwa [sub_ne_zero, ne_comm]
      simp [h, this]
  simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

-- Convolution is commutative: conv f g = conv g f.
-- Reindexing via k -> n - k using Equiv.subLeft.
theorem conv_comm (f g : Signal N) : conv f g = conv g f := by
  ext n
  simp only [conv]
  exact Fintype.sum_equiv (Equiv.subLeft n) _ _ (fun k => by
    simp [Equiv.subLeft_apply, mul_comm])

-- Convolution distributes over addition: conv f (g + h) = conv f g + conv f h.
omit [NeZero N] in
theorem conv_add (f g h : Signal N) : conv f (g + h) = conv f g + conv f h := by
  ext n
  simp only [conv, Pi.add_apply, mul_add, Finset.sum_add_distrib]

-- Convolution distributes over addition in the first argument.
theorem add_conv (f g h : Signal N) : conv (f + g) h = conv f h + conv g h := by
  rw [conv_comm (f + g) h, conv_add, conv_comm h f, conv_comm h g]

-- Convolution respects scalar multiplication: conv f (a * g) = a * (conv f g).
omit [NeZero N] in
theorem conv_smul (f g : Signal N) (a : ℝ) : conv f (a • g) = a • conv f g := by
  ext n
  simp only [conv, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ k : Fin N, f k * (a * g (n - k))) = a * ∑ k : Fin N, f k * g (n - k) from by
    rw [Finset.mul_sum]; congr 1; ext k; ring]

-- Convolution is associative: conv (conv f g) h = conv f (conv g h).
-- Proof strategy: distribute, swap the double sum, reindex via Equiv.subRight.
theorem conv_assoc (f g h : Signal N) :
    conv (conv f g) h = conv f (conv g h) := by
  ext n
  simp only [conv]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext k
  exact Fintype.sum_equiv (Equiv.subRight k)
    (fun j => f k * g (j - k) * h (n - j))
    (fun j => f k * (g j * h (n - k - j)))
    (fun j => by
      simp only [Equiv.subRight_apply]
      have : n - k - (j - k) = n - j := by abel
      rw [this, mul_assoc])

end SpatialAudio
