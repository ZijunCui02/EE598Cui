# EE598 Automated Math -- [Zijun Cui](https://zijuncui.com)

## Course Project: Formalizing Spatial Audio DSP Foundations in Lean 4

### Goal

Formalize the mathematical foundations of spatial audio processing in Lean 4
using Mathlib. The project covers discrete circular convolution and its
algebraic structure, the Woodworth interaural time difference model with
calculus-based monotonicity, first-order Ambisonics rotation matrices with
group structure, and a binaural rendering pipeline connecting these components.

### File Structure

All project code is in the `project/` directory:

| File | Description |
|------|-------------|
| `project/SpatialAudio/Convolution.lean` | Signal type, convolution, algebraic properties including associativity |
| `project/SpatialAudio/ITD.lean` | Woodworth ITD model, symmetry, derivative, monotonicity |
| `project/SpatialAudio/Ambisonics.lean` | Z-axis rotation matrix, orthogonality, group structure, monoid homomorphism |
| `project/SpatialAudio/Rendering.lean` | FOA signal and HRTF types, rotation, binaural rendering, ITD-sample connection |
| `project/SpatialAudio.lean` | Root import file |

### Main Definitions

| Definition | File | Description |
|---|---|---|
| `Signal N` | Convolution | Discrete signal of length N: `Fin N -> R` |
| `delta` | Convolution | Kronecker delta signal: 1 at index 0, 0 elsewhere |
| `conv f g` | Convolution | Circular convolution via modular-arithmetic indexing on Fin N |
| `ITD r c theta` | ITD | Woodworth interaural time difference: `(r/c)(theta + sin theta)` |
| `rotZ alpha` | Ambisonics | 3x3 z-axis rotation matrix for first-order Ambisonics |
| `rotZHom` | Ambisonics | Monoid homomorphism from `(R, +)` to `(Mat_3, *)` witnessing group structure |
| `FOASignal N` | Rendering | First-order Ambisonics signal with W, X, Y channels |
| `HRTFSet N` | Rendering | Head-related transfer function filter set for binaural decoding |
| `rotateFOA alpha sig` | Rendering | Rotate an FOA signal by angle alpha around the vertical axis |
| `renderEar sig hrtf` | Rendering | Binaural rendering: convolve each channel with its HRTF and sum |
| `itdSamples r c fs theta` | Rendering | ITD in samples at sample rate fs, connecting ITD to the signal pipeline |

### Main Theorems

| Theorem | File | Statement |
|---|---|---|
| `conv_delta` | Convolution | `conv f delta = f` (delta identity) |
| `conv_comm` | Convolution | `conv f g = conv g f` (commutativity) |
| `conv_assoc` | Convolution | `conv (conv f g) h = conv f (conv g h)` (associativity) |
| `conv_add` | Convolution | `conv f (g + h) = conv f g + conv f h` (additive linearity) |
| `add_conv` | Convolution | `conv (f + g) h = conv f h + conv g h` (left additive linearity) |
| `conv_smul` | Convolution | `conv f (a * g) = a * conv f g` (scalar linearity) |
| `ITD_zero` | ITD | `ITD r c 0 = 0` (zero delay at zero azimuth) |
| `ITD_neg` | ITD | `ITD r c (-theta) = -ITD r c theta` (odd symmetry) |
| `hasDerivAt_ITD` | ITD | Derivative is `(r/c)(1 + cos theta)` |
| `ITD_monotoneOn` | ITD | ITD is monotone on `[0, pi/2]` for positive r, c |
| `rotZ_orthogonal` | Ambisonics | `rotZ(alpha)^T * rotZ(alpha) = I` (energy preservation) |
| `rotZ_det` | Ambisonics | `det(rotZ(alpha)) = 1` (proper rotation) |
| `rotZ_mul` | Ambisonics | `rotZ(alpha) * rotZ(beta) = rotZ(alpha + beta)` (composition) |
| `rotZ_zero` | Ambisonics | `rotZ 0 = I` (identity element) |
| `rotZ_neg` | Ambisonics | `rotZ(alpha) * rotZ(-alpha) = I` (inverse) |
| `rotateFOA_zero` | Rendering | Zero rotation is identity on FOA signals |
| `rotateFOA_comp` | Rendering | `rotateFOA a (rotateFOA b sig) = rotateFOA (a + b) sig` |
| `renderEar_rotateFOA_zero` | Rendering | Rendering commutes with identity rotation |
| `renderEar_add` | Rendering | `renderEar (s1 + s2) h = renderEar s1 h + renderEar s2 h` (linearity) |
| `itdSamples_zero` | Rendering | `itdSamples r c fs 0 = 0` (zero delay straight ahead) |
| `itdSamples_neg` | Rendering | `itdSamples r c fs (-theta) = -itdSamples r c fs theta` (symmetry) |

### Building

Requires Lean v4.27.0-rc1 and Mathlib.

```
lake build SpatialAudio
```

### References

- Woodworth, R. S. (1938). *Experimental Psychology*. Holt.
- Zotter, F. and Frank, M. (2019). *Ambisonics: A Practical 3D Audio Theory
  for Recording, Studio Production, Sound Reinforcement, and Virtual Reality*.
  Springer.
- The Mathlib Community. *Mathlib4*.
  https://leanprover-community.github.io/mathlib4_docs/

### Future Work

- Higher-order Ambisonics: extend rotation to arbitrary spherical harmonic
  order and prove the relationship between Ambisonics order and spatial
  reconstruction accuracy
- Convolution theorem: relate circular convolution to pointwise DFT
  multiplication
- HRTF interpolation: formalize interpolation between measured HRTF directions
  using the ITD model
- Linear-phase FIR filters: formalize symmetry conditions and constant group
  delay
