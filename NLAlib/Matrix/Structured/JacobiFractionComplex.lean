import NLAlib.Matrix.Structured.JacobiAlgebra
import NLAlib.Matrix.Functions.ComplexResolvent

/-! # Complex Jacobi resolvents and nonvanishing fraction denominators

Every real symmetric trailing block is invertible at a nonreal shift. The actual
finite fraction and every ordinary scalar denominator are therefore well-defined.
The characteristic determinant quotient also covers real intermediate poles.
-/

noncomputable section
open Matrix Polynomial
open scoped Matrix
namespace NLAlib

/-- A nonreal shift of any actual real Hermitian matrix has nonzero determinant;
the empty matrix is included. Source: operator derivations (OF25).
atlas: jacobi-matrix-identities (partial) -/
theorem det_smul_one_sub_map_ne_zero_of_im_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (z • (1 : Matrix ι ι ℂ) - A.map Complex.ofRealHom).det ≠ 0 := by
  have he : Matrix.scalar ι z = z • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
  rw [← he, ← Matrix.eval_charpoly, Matrix.charpoly_map, hA.charpoly_eq,
    Polynomial.map_prod, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    eval_sub, eval_X, eval_C]
  apply sub_ne_zero.mpr
  intro h
  exact hz (by simpa only [Complex.ofRealHom_eq_coe, Complex.ofReal_im] using congrArg Complex.im h)

/-- The literal complex nested Jacobi fraction is the actual resolvent entry
at every nonreal argument. All intermediate determinants are nonzero by Hermitian
symmetry, without any off-diagonal sign restriction. Source: operator derivations (OF25).
atlas: jacobi-matrix-identities (partial) -/
theorem inv_smul_one_sub_map_jacobiMatrix_apply_zero_zero (a β : ℕ → ℝ) (m : ℕ)
    {z : ℂ} (hz : z.im ≠ 0) :
    (z • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) -
      (jacobiMatrix a β (m + 1)).map Complex.ofRealHom)⁻¹ 0 0 =
        jacobiFraction (Complex.ofRealHom ∘ a) (Complex.ofRealHom ∘ β) z (m + 1) 0 := by
  induction m generalizing a β with
  | zero => rw [map_jacobiMatrix, inv_apply_zero_zero, det_fin_one]; simp [jacobiFraction, jacobiMatrix]
  | succ m ih =>
    let a' := fun i => a (i + 1)
    let β' := fun i => β (i + 1)
    have hd1 := det_smul_one_sub_map_ne_zero_of_im_ne_zero (isHermitian_jacobiMatrix a' β' (m + 1)) hz
    have ih' := ih a' β'
    rw [map_jacobiMatrix, inv_apply_zero_zero,
      submatrix_succ_smul_one_sub_jacobiMatrix] at ih'
    rw [map_jacobiMatrix, inv_apply_zero_zero,
      submatrix_succ_smul_one_sub_jacobiMatrix, det_smul_one_sub_jacobiMatrix,
      jacobiFraction, jacobiFraction_succ]
    change _ = 1 / (z - Complex.ofRealHom (a 0) - Complex.ofRealHom (β 1) ^ 2 *
      jacobiFraction (Complex.ofRealHom ∘ a') (Complex.ofRealHom ∘ β') z (m + 1) 0)
    rw [← ih']
    rw [map_jacobiMatrix] at hd1
    simp only [a', β', Function.comp_def] at *
    field_simp [hd1]

/-- For every complex argument, the actual Jacobi resolvent entry is the ratio
of its trailing and full characteristic determinants. In particular, at real
intermediate fraction poles this uses the final determinant rather than a false
literal nested equality. Source: operator derivations (OF26).
atlas: jacobi-matrix-identities (partial) -/
theorem inv_smul_one_sub_map_jacobiMatrix_apply_zero_zero_eq_det_ratio
    (a β : ℕ → ℝ) (m : ℕ) (z : ℂ) :
    (z • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) -
      (jacobiMatrix a β (m + 1)).map Complex.ofRealHom)⁻¹ 0 0 =
      (z • (1 : Matrix (Fin m) (Fin m) ℂ) -
        (jacobiMatrix (fun i => a (i + 1)) (fun i => β (i + 1)) m).map Complex.ofRealHom).det /
      (z • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) -
        (jacobiMatrix a β (m + 1)).map Complex.ofRealHom).det := by
  rw [inv_apply_zero_zero]
  congr 1
  rw [map_jacobiMatrix, submatrix_succ_smul_one_sub_jacobiMatrix, map_jacobiMatrix]
  rfl

/-- Every positive-length complex Jacobi fraction at a nonreal argument is
nonzero, since its actual trailing and full determinants are both nonzero.
Source: operator derivations (OF25)–(OF26).
atlas: jacobi-matrix-identities (partial) -/
theorem jacobiFraction_map_ne_zero_of_im_ne_zero (a β : ℕ → ℝ) (m : ℕ)
    {z : ℂ} (hz : z.im ≠ 0) :
    jacobiFraction (Complex.ofRealHom ∘ a) (Complex.ofRealHom ∘ β) z (m + 1) 0 ≠ 0 := by
  rw [← inv_smul_one_sub_map_jacobiMatrix_apply_zero_zero a β m hz,
    inv_smul_one_sub_map_jacobiMatrix_apply_zero_zero_eq_det_ratio]
  exact div_ne_zero
    (det_smul_one_sub_map_ne_zero_of_im_ne_zero
      (isHermitian_jacobiMatrix (fun i => a (i + 1)) (fun i => β (i + 1)) m) hz)
    (det_smul_one_sub_map_ne_zero_of_im_ne_zero (isHermitian_jacobiMatrix a β (m + 1)) hz)

/-- Every scalar Schur denominator of the literal nonreal fraction is nonzero.
Applying this theorem to each shifted coefficient family gives all its internal
denominators. Source: operator derivations (OF25).
atlas: jacobi-matrix-identities (partial) -/
theorem jacobiFraction_step_denominator_ne_zero_of_im_ne_zero (a β : ℕ → ℝ) (m : ℕ)
    {z : ℂ} (hz : z.im ≠ 0) :
    z - Complex.ofRealHom (a 0) - Complex.ofRealHom (β 1) ^ 2 *
      jacobiFraction (Complex.ofRealHom ∘ a) (Complex.ofRealHom ∘ β) z m 1 ≠ 0 := by
  apply ne_zero_of_one_div_ne_zero
  simpa only [jacobiFraction, Function.comp_apply, Nat.zero_add] using
    jacobiFraction_map_ne_zero_of_im_ne_zero a β m hz

end NLAlib
