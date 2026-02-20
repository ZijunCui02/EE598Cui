# EE598 Automated Math — Zijun Cui

## Course Project: Formalizing Binaural Audio DSP in Lean 4

Formalization of binaural audio digital signal processing foundations in Lean 4 using Mathlib. Part A (core) defines discrete signals, discrete convolution, and proves algebraic properties (commutativity, associativity, linearity, delta identity), defines HRTF filtering as convolution, and formalizes the Woodworth ITD model ITD(θ) = (r/c)(θ + sin θ) with proofs of symmetry and monotonicity. Part B (stretch) defines first-order Ambisonics rotation matrices and proves orthogonality, det = 1, and rotation composition.
