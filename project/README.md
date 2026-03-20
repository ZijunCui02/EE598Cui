# Spatial Audio DSP Foundations

Lean 4 formalization of the core mathematics behind spatial audio processing.

## Structure

- `SpatialAudio/Convolution.lean` -- Discrete circular convolution on `Fin N -> R` with
  delta identity, commutativity, associativity, and linearity.
- `SpatialAudio/ITD.lean` -- Woodworth spherical head model `ITD(theta) = (r/c)(theta + sin theta)`
  with symmetry, derivative, and monotonicity on `[0, pi/2]`.
- `SpatialAudio/Ambisonics.lean` -- First-order Ambisonics z-axis rotation matrix with
  orthogonality, det = 1, composition, identity, inverse, and a monoid homomorphism
  from `(R, +)` to `(Mat_3, *)`.
- `SpatialAudio/Rendering.lean` -- Binaural rendering pipeline connecting all three
  modules: FOA signal rotation, HRTF convolution, ITD-to-sample-delay bridge,
  and composition theorems.

## Build

```
lake build SpatialAudio
```
