import TroppMatrixConcentration.Defs.Spectral

namespace TroppMatrixConcentration

def dilation {m n : Type*} (A : Matrix m n ℂ) :
    Matrix (Sum m n) (Sum m n) ℂ := Matrix.fromBlocks 0 A A.conjTranspose 0

end TroppMatrixConcentration
