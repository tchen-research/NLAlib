import NLAlib.Matrix.Functions.UnitaryCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Complex-valued functional calculus for matrix powers

Complex powers are the native normal-matrix continuous functional calculus
of the principal scalar complex power. For PSD inputs and exponents with
positive real part, zero eigenvalues contribute zero.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Theorem 3.2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Matrix Complex
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every complex-valued function on the finite normal spectrum commutes
with actual unitary conjugation. -/
theorem cfc_complex_unitary_conj (U : unitary (Matrix n n ℂ)) (f : ℂ → ℂ)
    (A : Matrix n n ℂ) (hA : IsStarNormal A) :
    cfc f ((U : Matrix n n ℂ) * A * (U : Matrix n n ℂ)ᴴ) =
      (U : Matrix n n ℂ) * cfc f A * (U : Matrix n n ℂ)ᴴ := by
  cases isEmpty_or_nonempty n with
  | inl h =>
    let := h
    exact Subsingleton.elim _ _
  | inr h =>
    let := h
    let E := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
    symm
    change E (cfc f A) = cfc f (E A)
    exact StarAlgHomClass.map_cfc E f A (A.finite_spectrum.continuousOn f)
      E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional hA (hA.map E)

/-- The native principal complex power of a normal matrix. In particular,
this is the source's complex power for PSD matrices; no logarithm is taken
at their zero eigenvalues when the exponent has positive real part. -/
def matrixComplexPower (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  cfc (fun w : ℂ => w ^ z) A

/-- Native matrix complex powers keep their scalar spectral meaning under
unitary changes of coordinates. -/
theorem matrixComplexPower_unitary_conj (U : unitary (Matrix n n ℂ))
    (A : Matrix n n ℂ) (hA : IsStarNormal A) (z : ℂ) :
    matrixComplexPower ((U : Matrix n n ℂ) * A * (U : Matrix n n ℂ)ᴴ) z =
      (U : Matrix n n ℂ) * matrixComplexPower A z * (U : Matrix n n ℂ)ᴴ :=
  cfc_complex_unitary_conj U _ A hA

set_option backward.isDefEq.respectTransparency false in
/-- Complex functional calculus acts entrywise on an arbitrary complex diagonal.
No continuity assumption is needed on its finite spectrum. -/
theorem cfc_diagonal_complex (f : ℂ → ℂ) (x : n → ℂ) :
    cfc f (Matrix.diagonal x) = Matrix.diagonal (fun i => f (x i)) := by
  let := IsStarNormal.instContinuousFunctionalCalculus (A := n → ℂ)
  have hx : IsStarNormal x := by infer_instance
  have hd : IsStarNormal (diagonalStarAlgHom x) := hx.map diagonalStarAlgHom
  have hc : ContinuousOn f (spectrum ℂ x) := by
    rw [Pi.spectrum_eq]
    have heq : (⋃ i, spectrum ℂ (x i)) = Set.range x := by
      change (⋃ i, spectrum ℂ (algebraMap ℂ ℂ (x i))) = _
      simp only [spectrum.scalar_eq, Set.iUnion_singleton_eq_range]
    rw [heq]
    exact Set.Finite.continuousOn (Set.finite_range _) _
  have heq := diagonalStarAlgHom.map_cfc (p := IsStarNormal) (q := IsStarNormal) f x hc
    (by change Continuous (fun z : n → ℂ => Matrix.diagonal z); fun_prop) hx hd
  rw [cfc_map_pi (p := IsStarNormal) (q := fun _ => IsStarNormal) (S := ℂ) f x
    (by rwa [← Pi.spectrum_eq]) hx (fun _ => inferInstance)] at heq
  change Matrix.diagonal (fun i => cfc f (algebraMap ℂ ℂ (x i))) =
    cfc f (Matrix.diagonal x) at heq
  have hh (i : n) : cfc f (x i) = f (x i) := cfc_algebraMap (R := ℂ) (A := ℂ) (x i) f
  simp only [Algebra.algebraMap_self, RingHom.id_apply, hh] at heq
  exact heq.symm

/-- A Hermitian matrix's native complex calculus is evaluation at its real
spectrum in one fixed orthonormal eigenbasis. -/
theorem cfc_complex_eq_eigenbasis {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℂ → ℂ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => f (hA.eigenvalues i : ℂ)) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    cfc_complex_unitary_conj, cfc_diagonal_complex]
  · rfl
  · exact (Matrix.isHermitian_diagonal_of_self_adjoint _
      (by ext i; simp)).isSelfAdjoint.isStarNormal

/-- Native complex powers evaluate the scalar principal power at every
Hermitian eigenvalue, with multiplicity. -/
theorem matrixComplexPower_eq_eigenbasis {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (z : ℂ) :
    matrixComplexPower A z = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ) ^ z) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ :=
  cfc_complex_eq_eigenbasis hA _

/-- Scalar shifts retain a fixed Hermitian eigenbasis, including at repeated
eigenvalues. -/
theorem add_ofReal_smul_one_eq_eigenbasis {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (ε : ℝ) :
    A + (ε : ℂ) • (1 : Matrix n n ℂ) =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun i => ((hA.eigenvalues i + ε : ℝ) : ℂ)) *
          (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  let E := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary
  have hd : Matrix.diagonal (fun i => ((hA.eigenvalues i + ε : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) +
        (ε : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  change A + (ε : ℂ) • 1 = E _
  rw [hd, map_add, map_smul, map_one]
  congr 1
  exact hA.spectral_theorem

/-- A shifted Hermitian matrix's complex power in its original eigenbasis.
This formula avoids choosing eigenvectors separately at each shift. -/
theorem matrixComplexPower_add_ofReal_smul_one {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (ε : ℝ) (z : ℂ) :
    matrixComplexPower (A + (ε : ℂ) • (1 : Matrix n n ℂ)) z =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun i => ((hA.eigenvalues i + ε : ℝ) : ℂ) ^ z) *
          (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  rw [add_ofReal_smul_one_eq_eigenbasis hA ε, matrixComplexPower_unitary_conj]
  · exact congrArg (fun X : Matrix n n ℂ =>
      (hA.eigenvectorUnitary : Matrix n n ℂ) * X *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
      (cfc_diagonal_complex (fun w => w ^ z) _)
  · exact (Matrix.isHermitian_diagonal_of_self_adjoint _
      (by ext i; simp)).isSelfAdjoint.isStarNormal

/-- Complex powers are continuous under scalar regularization of a fixed
Hermitian matrix when the exponent has positive real part. In particular,
this includes all zero eigenvalues of a PSD input. -/
theorem continuousAt_matrixComplexPower_add_ofReal_smul_one
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt (fun ε : ℝ => matrixComplexPower
      (A + (ε : ℂ) • (1 : Matrix n n ℂ)) z) 0 := by
  simp_rw [matrixComplexPower_add_ofReal_smul_one hA]
  have hc : Continuous (fun ε : ℝ => fun i : n =>
      ((hA.eigenvalues i + ε : ℝ) : ℂ) ^ z) := by
    apply continuous_pi
    intro i
    exact (Complex.continuous_ofReal_cpow_const hz).comp (by fun_prop)
  apply ContinuousAt.mul
  · apply ContinuousAt.mul continuousAt_const
    exact ((Matrix.diagonalLinearMap n ℂ ℂ).continuous_of_finiteDimensional.comp hc).continuousAt
  · exact continuousAt_const

/-- The ordinary exponential acts entrywise on complex diagonal matrices. -/
theorem matrixExp_diagonal_complex (x : n → ℂ) :
    matrixExp (Matrix.diagonal x) = Matrix.diagonal (fun i => Complex.exp (x i)) := by
  have hd : IsStarNormal (Matrix.diagonal x) := by
    let := IsStarNormal.instContinuousFunctionalCalculus (A := n → ℂ)
    exact (show IsStarNormal x from inferInstance).map diagonalStarAlgHom
  rw [matrixExp, ← CFC.complex_exp_eq_normedSpace_exp hd, cfc_diagonal_complex]

/-- For positive definite matrices the native principal complex power equals
the exponential of the complex scalar times the real matrix logarithm. -/
theorem matrixComplexPower_eq_matrixExp_smul_log {A : Matrix n n ℂ}
    (hA : A.PosDef) (z : ℂ) :
    matrixComplexPower A z = matrixExp (z • matrixLog A) := by
  have hlog : matrixLog A = (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => (Real.log (hA.isHermitian.eigenvalues i) : ℂ)) *
        (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    rw [matrixLog, hA.isHermitian.cfc_eq]
    rfl
  rw [matrixComplexPower_eq_eigenbasis hA.isHermitian, hlog]
  rw [← smul_mul_assoc, ← mul_smul_comm, matrixExp_unitary_conj,
    ← Matrix.diagonal_smul, matrixExp_diagonal_complex]
  apply congrArg (fun X : Matrix n n ℂ =>
    (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * X *
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
  apply congrArg Matrix.diagonal
  funext i
  have hpos : 0 < hA.isHermitian.eigenvalues i := hA.eigenvalues_pos i
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
    ← Complex.ofReal_log hpos.le]
  simp [smul_eq_mul, mul_comm]

/-- Native real powers of a PSD matrix agree with its principal complex
power at real exponents. Zero eigenvalues retain the scalar power convention. -/
theorem matrixComplexPower_ofReal_eq_rpow {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (r : ℝ) :
    matrixComplexPower A (r : ℂ) = CFC.rpow A r := by
  rw [matrixComplexPower_eq_eigenbasis hA.isHermitian,
    show CFC.rpow A r = cfc (fun x : ℝ => x ^ r) A from
      CFC.rpow_eq_cfc_real hA.nonneg, hA.isHermitian.cfc_eq]
  change _ = (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
    Matrix.diagonal (fun i => ((hA.isHermitian.eigenvalues i ^ r : ℝ) : ℂ)) *
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ
  apply congrArg (fun X : Matrix n n ℂ =>
    (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * X *
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
  apply congrArg Matrix.diagonal
  funext i
  exact (Complex.ofReal_cpow (hA.eigenvalues_nonneg i) r).symm

omit [Fintype n] in
/-- Every positive scalar regularization of a PSD matrix is positive
definite. The scalar field is complex so this matches complex power formulas. -/
theorem posDef_add_ofReal_smul_one {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    (A + (ε : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
  Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul (by exact_mod_cast hε))

/-- On the right boundary, a PSD matrix's complex powers have operator norm
at most the original operator norm, uniformly in imaginary time. -/
theorem norm_matrixComplexPower_le_of_re_eq_one {A : Matrix n n ℂ}
    (hA : A.PosSemidef) {z : ℂ} (hz : z.re = 1) :
    ‖matrixComplexPower A z‖ ≤ ‖A‖ := by
  apply norm_cfc_le (norm_nonneg A)
  intro w hw
  rw [hA.isHermitian.spectrum_eq_image_range] at hw
  obtain ⟨x, ⟨i, rfl⟩, rfl⟩ := hw
  let : Nonempty n := ⟨i⟩
  change ‖(hA.isHermitian.eigenvalues i : ℂ) ^ z‖ ≤ ‖A‖
  have hi : (hA.isHermitian.eigenvalues i : ℂ) ∈ spectrum ℂ A :=
    (spectrum.algebraMap_mem_iff ℂ).mpr (hA.isHermitian.eigenvalues_mem_spectrum_real i)
  have h := spectrum.norm_le_norm_of_mem hi
  calc
    _ = hA.isHermitian.eigenvalues i ^ z.re :=
      Complex.norm_cpow_eq_rpow_re_of_nonneg (hA.eigenvalues_nonneg i) (by rw [hz]; norm_num)
    _ = hA.isHermitian.eigenvalues i := by rw [hz, Real.rpow_one]
    _ ≤ ‖A‖ := by simpa [abs_of_nonneg (hA.eigenvalues_nonneg i)] using h

/-- Ordered imaginary powers of a PSD matrix vary continuously along the
right boundary, including when the matrix is singular. -/
theorem continuous_matrixComplexPower_right {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    Continuous (fun t : ℝ => matrixComplexPower A (1 + (t : ℂ) * I)) := by
  have hc (i : n) : Continuous (fun t : ℝ =>
      (hA.isHermitian.eigenvalues i : ℂ) ^ (1 + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have ht : ContinuousAt (fun s : ℝ =>
        (hA.isHermitian.eigenvalues i, 1 + (s : ℂ) * I)) t := by fun_prop
    have hfull := Complex.continuousAt_ofReal_cpow (hA.isHermitian.eigenvalues i)
      (1 + (t : ℂ) * I) (Or.inl (by simp))
    have hcomp := ContinuousAt.comp
      (f := fun s : ℝ => (hA.isHermitian.eigenvalues i, 1 + (s : ℂ) * I))
      (g := fun p : ℝ × ℂ => (p.1 : ℂ) ^ p.2) hfull ht
    exact hcomp
  simp_rw [matrixComplexPower_eq_eigenbasis hA.isHermitian]
  have hpi : Continuous (fun t : ℝ => fun i : n =>
      (hA.isHermitian.eigenvalues i : ℂ) ^ (1 + (t : ℂ) * I)) := continuous_pi hc
  exact (continuous_const.mul
    ((Matrix.diagonalLinearMap n ℂ ℂ).continuous_of_finiteDimensional.comp hpi)).mul
      continuous_const

end NLAlib
