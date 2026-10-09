import NLAlib.Concentration.Matrix.Defs.Spectral

/-!
# Hermitian dilation

The Hermitian dilation of a rectangular complex matrix.

Atlas: `hermitian-dilation`.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8* (Tropp 2015).
-/

namespace NLAlib

/-- The Hermitian dilation `fromBlocks 0 A Aᴴ 0` of a rectangular matrix `A`. Tropp 2015, Def. 2.1.5.
Atlas: `hermitian-dilation`. -/
def dilation {m n : Type*} (A : Matrix m n ℂ) :
    Matrix (Sum m n) (Sum m n) ℂ := Matrix.fromBlocks 0 A A.conjTranspose 0

end NLAlib
