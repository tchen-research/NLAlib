import NLAlib.Matrix.Functions.PolynomialIntertwining
import NLAlib.Matrix.Spectral.EigenvectorPairing

/-!
# Qualitative Sylvester equations

The Bézout proof of uniqueness and existence requires no Schur or Jordan form.
It works over every field with coprime characteristic polynomials, including
real data and empty rectangular spaces. Source: Horn–Johnson (2013), §0.7.7,
Lemma 2.4.4.0 and Theorem 2.4.4.1; atlas `sylvester-equation`.
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {K : Type*} [Field K]

/-- The rectangular Sylvester operator. Source: Horn–Johnson (2013),
Theorem 2.4.4.1; the definition includes zero-dimensional matrix spaces. -/
def sylvesterLinearMap (A : Matrix m m K) (B : Matrix n n K) :
    Matrix m n K →ₗ[K] Matrix m n K where
  toFun X := A * X - X * B
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, RingHom.id_apply]

/-- Coprime characteristic polynomials annihilate every rectangular intertwiner.
Source: Horn–Johnson (2013), Lemma 2.4.4.0 and Theorem 2.4.4.1, using Bézout
and Cayley–Hamilton instead of a triangular basis.
atlas: sylvester-equation (partial) -/
theorem eq_zero_of_mul_eq_mul_of_isCoprime_charpoly {A : Matrix m m K}
    {B : Matrix n n K} (hcop : IsCoprime A.charpoly B.charpoly)
    {X : Matrix m n K} (hX : A * X = X * B) : X = 0 := by
  obtain ⟨p, q, hpq⟩ := hcop
  have hB : aeval A B.charpoly * X = 0 := by
    rw [aeval_mul_eq_mul_aeval_of_mul_eq hX, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  have heval := congrArg (aeval A) hpq
  have hid : aeval A q * aeval A B.charpoly = 1 := by
    simpa only [map_add, map_mul, map_one, Matrix.aeval_self_charpoly,
      Matrix.mul_zero, zero_add] using heval
  calc
    X = (aeval A q * aeval A B.charpoly) * X := by rw [hid, Matrix.one_mul]
    _ = 0 := by rw [Matrix.mul_assoc, hB, Matrix.mul_zero]

/-- The Sylvester operator is bijective for coprime characteristic polynomials.
Source: Horn–Johnson (2013), Theorem 2.4.4.1; finite dimensionality converts
the Bézout kernel computation into surjectivity.
atlas: sylvester-equation (partial) -/
theorem sylvesterLinearMap_bijective_of_isCoprime_charpoly (A : Matrix m m K)
    (B : Matrix n n K) (hcop : IsCoprime A.charpoly B.charpoly) :
    Function.Bijective (sylvesterLinearMap A B) := by
  have hinj : Function.Injective (sylvesterLinearMap A B) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro X hX
    exact eq_zero_of_mul_eq_mul_of_isCoprime_charpoly hcop (sub_eq_zero.mp hX)
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- Every right-hand side has exactly one solution to the Sylvester equation
when the characteristic polynomials are coprime. Source: Horn–Johnson (2013),
Theorem 2.4.4.1; real fields and empty shapes are included directly.
atlas: sylvester-equation (partial) -/
theorem existsUnique_sylvester_of_isCoprime_charpoly (A : Matrix m m K)
    (B : Matrix n n K) (hcop : IsCoprime A.charpoly B.charpoly) (C : Matrix m n K) :
    ∃! X : Matrix m n K, A * X - X * B = C := by
  obtain ⟨X, hX⟩ := (sylvesterLinearMap_bijective_of_isCoprime_charpoly A B hcop).2 C
  refine ⟨X, hX, fun Y hY => ?_⟩
  exact (sylvesterLinearMap_bijective_of_isCoprime_charpoly A B hcop).1 (hY.trans hX.symm)

/-- Over an algebraically closed field, spectral disjointness is exactly
coprimality of characteristic polynomials. Source: Horn–Johnson (2013),
Theorem 2.4.4.1; empty spectra cause no exception. -/
theorem isCoprime_charpoly_iff_disjoint_spectrum [IsAlgClosed K]
    (A : Matrix m m K) (B : Matrix n n K) :
    IsCoprime A.charpoly B.charpoly ↔ Disjoint (spectrum K A) (spectrum K B) := by
  classical
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K A.charpoly B.charpoly,
    Set.disjoint_left]
  simp only [Polynomial.coe_aeval_eq_eval,
    Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot]
  constructor
  · intro h a ha
    exact (h a).resolve_left (not_not.mpr ha)
  · intro h a
    by_cases ha : A.charpoly.eval a = 0
    · exact Or.inr (h ha)
    · exact Or.inl ha

/-- The Sylvester operator is injective exactly when the spectra are disjoint.
Source: Horn–Johnson (2013), Theorem 2.4.4.1; a common eigenvalue supplies a
nonzero outer-product kernel element, while Bézout proves the converse.
atlas: sylvester-equation (partial) -/
theorem sylvesterLinearMap_injective_iff_disjoint_spectrum [IsAlgClosed K]
    (A : Matrix m m K) (B : Matrix n n K) :
    Function.Injective (sylvesterLinearMap A B) ↔
      Disjoint (spectrum K A) (spectrum K B) := by
  constructor
  · intro hinj
    apply Set.disjoint_left.mpr
    intro μ hA hB
    obtain ⟨x, hx, hAx⟩ := exists_mulVec_eq_smul_of_mem_spectrum hA
    obtain ⟨y, hy, hyB⟩ := exists_vecMul_eq_smul_of_mem_spectrum hB
    have hXY : sylvesterLinearMap A B (Matrix.vecMulVec x y) =
        sylvesterLinearMap A B 0 := by
      change A * Matrix.vecMulVec x y - Matrix.vecMulVec x y * B =
        A * (0 : Matrix m n K) - (0 : Matrix m n K) * B
      rw [mul_vecMulVec_eq_vecMulVec_mul hAx hyB, sub_self, Matrix.mul_zero,
        Matrix.zero_mul, sub_self]
    exact vecMulVec_ne_zero hx hy (hinj hXY)
  · intro hdisj
    exact (sylvesterLinearMap_bijective_of_isCoprime_charpoly A B
      ((isCoprime_charpoly_iff_disjoint_spectrum A B).mpr hdisj)).1

/-- The Sylvester operator is invertible exactly for disjoint spectra.
Source: Horn–Johnson (2013), Theorem 2.4.4.1; formulated as bijectivity to
avoid choosing an inverse and valid in dimension zero.
atlas: sylvester-equation (partial) -/
theorem sylvesterLinearMap_bijective_iff_disjoint_spectrum [IsAlgClosed K]
    (A : Matrix m m K) (B : Matrix n n K) :
    Function.Bijective (sylvesterLinearMap A B) ↔
      Disjoint (spectrum K A) (spectrum K B) := by
  rw [Function.Bijective, ← LinearMap.injective_iff_surjective, and_self,
    sylvesterLinearMap_injective_iff_disjoint_spectrum]

/-- Disjoint spectra give exactly one solution for each Sylvester right-hand
side. Source: Horn–Johnson (2013), Theorem 2.4.4.1; indices may be empty.
atlas: sylvester-equation (partial) -/
theorem existsUnique_sylvester_of_disjoint_spectrum [IsAlgClosed K]
    (A : Matrix m m K) (B : Matrix n n K)
    (hdisj : Disjoint (spectrum K A) (spectrum K B)) (C : Matrix m n K) :
    ∃! X : Matrix m n K, A * X - X * B = C :=
  existsUnique_sylvester_of_isCoprime_charpoly A B
    ((isCoprime_charpoly_iff_disjoint_spectrum A B).mpr hdisj) C

/-- An off-diagonal block intertwiner vanishes for disjoint block spectra.
Source: Horn–Johnson (2013), Corollary 2.4.4.2; the row and column blocks may
have different sizes.
atlas: sylvester-equation (partial) -/
theorem eq_zero_of_mul_eq_mul_of_disjoint_spectrum [IsAlgClosed K]
    {A : Matrix m m K} {B : Matrix n n K}
    (hdisj : Disjoint (spectrum K A) (spectrum K B)) {X : Matrix m n K}
    (hX : A * X = X * B) : X = 0 :=
  eq_zero_of_mul_eq_mul_of_isCoprime_charpoly
    ((isCoprime_charpoly_iff_disjoint_spectrum A B).mpr hdisj) hX

end NLAlib
