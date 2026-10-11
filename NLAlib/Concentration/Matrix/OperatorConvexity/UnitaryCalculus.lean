import NLAlib.Concentration.Matrix.Defs.Calculus
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Unitary covariance of matrix functional calculus

Unitary conjugation preserves Hermitian matrices, positivity, spectra, and traces.
The logarithm and every real continuous functional calculus on a finite spectrum
commute with conjugation. The exponential and trace exponential do so for all
complex square matrices. Reflection corollaries use the same general automorphism
API. All statements include empty finite index types.

Source: Tropp 2015, §2.1 and the unitary dilation proof of Theorem 8.5.2;
`Re-derivations/matrix_toolkit_operator_derivations.tex`, §7 and its implementation
map. The local private `unitary_calculus` proof in `JensenIsometricCompression`
provides the reflection specialization of the CFC transport argument.
Atlas: `golden-thompson`, `operator-monotone-convex` (supporting calculus).
-/

noncomputable section
set_option autoImplicit false

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unitary conjugation preserves Hermitian matrices. Source: unitary functional
calculus, Tropp 2015, §2.1; atlas `golden-thompson` (helper). -/
theorem isHermitian_unitary_conj (U : unitary (Matrix ι ι ℂ))
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix ι ι ℂ) hA

/-- Unitary conjugation preserves the real spectrum. Source: the conjugation
star-algebra automorphism; Tropp 2015, §2.1; atlas `golden-thompson` (helper). -/
theorem spectrum_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    spectrum ℝ ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) = spectrum ℝ A := by
  exact AlgEquiv.spectrum_eq (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) U).toAlgEquiv A

/-- Every real function on a Hermitian matrix's finite spectrum commutes with
unitary conjugation. No global continuity premise is needed. Source: Mathlib's
CFC transport and Tropp 2015, Theorem 8.5.2; atlas `golden-thompson`,
`operator-monotone-convex` (helper). -/
theorem cfc_unitary_conj (U : unitary (Matrix ι ι ℂ)) (f : ℝ → ℝ)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    cfc f ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) =
      (U : Matrix ι ι ℂ) * cfc f A * (U : Matrix ι ι ℂ)ᴴ := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let := h
      exact Subsingleton.elim _ _
  | inr h =>
      let := h
      let E := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) U
      symm
      change E (cfc f A) = cfc f (E A)
      exact StarAlgHomClass.map_cfc E f A (A.finite_real_spectrum.continuousOn f)
        E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional hA
        (isHermitian_unitary_conj U A hA)

/-- Matrix logarithms commute with unitary conjugation of Hermitian matrices.
Source: real logarithm functional calculus, Tropp 2015, §2.1.12;
atlas `golden-thompson` (helper). -/
theorem matrixLog_unitary_conj (U : unitary (Matrix ι ι ℂ))
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    matrixLog ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) =
      (U : Matrix ι ι ℂ) * matrixLog A * (U : Matrix ι ι ℂ)ᴴ :=
  cfc_unitary_conj U Real.log A hA

/-- Matrix exponentials commute with unitary conjugation, even without a
Hermitian premise. Source: continuous ring-homomorphism transport of the
exponential, Tropp 2015, §2.1.11; atlas `golden-thompson` (helper). -/
theorem matrixExp_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    matrixExp ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) =
      (U : Matrix ι ι ℂ) * matrixExp A * (U : Matrix ι ι ℂ)ᴴ := by
  let E := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  symm
  change E (NormedSpace.exp A) = NormedSpace.exp (E A)
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) E
    E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional A
    ((NormedSpace.expSeries_radius_eq_top ℂ (Matrix ι ι ℂ)).symm ▸ edist_lt_top _ _)

/-- The complex trace is unchanged by unitary conjugation. Source: cyclicity
of trace, Tropp 2015, §2.1; atlas `golden-thompson` (helper). -/
theorem trace_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    Matrix.trace ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) = Matrix.trace A := by
  rw [Matrix.trace_mul_cycle]
  simp only [← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, Matrix.one_mul]

/-- The real trace exponential is unchanged by unitary conjugation, for every
complex square matrix. Source: exponential covariance and trace cyclicity,
Tropp 2015, §3.1; atlas `golden-thompson` (helper). -/
theorem traceExp_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    traceExp ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) = traceExp A := by
  unfold traceExp
  rw [matrixExp_unitary_conj, trace_unitary_conj]

/-- Unitary conjugation preserves and reflects positive semidefiniteness.
Source: invertible congruence of Hermitian quadratic forms, Tropp 2015, §2.1.5;
atlas `golden-thompson` (helper). -/
theorem posSemidef_unitary_conj_iff (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ).PosSemidef ↔ A.PosSemidef :=
  Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe (U := U))

/-- Unitary conjugation preserves and reflects positive definiteness.
Source: invertible congruence of Hermitian quadratic forms, Tropp 2015, §2.1.5;
atlas `golden-thompson` (helper). -/
theorem posDef_unitary_conj_iff (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ).PosDef ↔ A.PosDef :=
  Matrix.IsUnit.posDef_star_right_conjugate_iff (Unitary.isUnit_coe (U := U))

/-- Simultaneous unitary conjugation leaves the Lieb trace function unchanged.
Only the logarithm's input needs to be Hermitian. Source: eigenbasis transport
in the operator derivations §7; atlas `golden-thompson` (helper). -/
theorem traceExp_add_matrixLog_unitary_conj (U : unitary (Matrix ι ι ℂ))
    (H A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    traceExp ((U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ)ᴴ +
      matrixLog ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ)) =
        traceExp (H + matrixLog A) := by
  let E := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  change traceExp (E H + matrixLog (E A)) = _
  have hlog : matrixLog (E A) = E (matrixLog A) := matrixLog_unitary_conj U A hA
  rw [hlog, ← map_add E]
  exact traceExp_unitary_conj U _

/-- The complex trace pairing of a matrix exponential and another matrix is
unchanged by simultaneous unitary conjugation. No Hermitian premises are needed.
Source: exponential covariance and trace cyclicity, operator derivations §7;
atlas `golden-thompson` (helper). -/
theorem trace_matrixExp_mul_unitary_conj (U : unitary (Matrix ι ι ℂ))
    (H A : Matrix ι ι ℂ) :
    Matrix.trace (matrixExp ((U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ)ᴴ) *
      ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ)) =
        Matrix.trace (matrixExp H * A) := by
  let E := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  change Matrix.trace (matrixExp (E H) * E A) = _
  have hexp : matrixExp (E H) = E (matrixExp H) := matrixExp_unitary_conj U H
  rw [hexp, ← map_mul E]
  exact trace_unitary_conj U _

/-- The real part of the trace pairing of a matrix exponential and another
matrix is invariant under simultaneous unitary conjugation. Source: operator
derivations §7; atlas `golden-thompson` (helper). -/
theorem re_trace_matrixExp_mul_unitary_conj (U : unitary (Matrix ι ι ℂ))
    (H A : Matrix ι ι ℂ) :
    (Matrix.trace (matrixExp ((U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ)ᴴ) *
      ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ))).re =
        (Matrix.trace (matrixExp H * A)).re :=
  congrArg Complex.re (trace_matrixExp_mul_unitary_conj U H A)

/-- The Lieb trace function is invariant under a unitary conjugation that fixes
its Hermitian parameter. Only the logarithm's input needs a Hermitian premise for
this identity. Source: midpoint pinching, operator derivations §7;
atlas `golden-thompson` (helper). -/
theorem traceExp_add_matrixLog_unitary_conj_of_conj_eq
    (U : unitary (Matrix ι ι ℂ)) (H A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hH : (U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ)ᴴ = H) :
    traceExp (H + matrixLog ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ)) =
      traceExp (H + matrixLog A) := by
  calc
    traceExp (H + matrixLog ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ)) =
        traceExp ((U : Matrix ι ι ℂ) * (H + matrixLog A) * (U : Matrix ι ι ℂ)ᴴ) := by
      rw [matrixLog_unitary_conj U A hA, Matrix.mul_add, Matrix.add_mul, hH]
    _ = traceExp (H + matrixLog A) := traceExp_unitary_conj U _

private theorem reflection_mem_unitary (R : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR2 : R * R = 1) : R ∈ unitary (Matrix ι ι ℂ) := by
  constructor <;> simpa only [Matrix.star_eq_conjTranspose, hR] using hR2

/-- Matrix logarithms commute with conjugation by a self-adjoint involution.
Source: reflection pinching, Tropp 2015, Theorem 8.5.2;
atlas `golden-thompson`, `operator-monotone-convex` (helper). -/
theorem matrixLog_reflection_conj (R A : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR2 : R * R = 1) (hA : A.IsHermitian) :
    matrixLog (R * A * R) = R * matrixLog A * R := by
  simpa only [hR] using
    matrixLog_unitary_conj ⟨R, reflection_mem_unitary R hR hR2⟩ A hA

/-- Matrix exponentials commute with conjugation by a self-adjoint involution.
Source: reflection pinching, Tropp 2015, Theorem 8.5.2;
atlas `golden-thompson`, `operator-monotone-convex` (helper). -/
theorem matrixExp_reflection_conj (R A : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR2 : R * R = 1) :
    matrixExp (R * A * R) = R * matrixExp A * R := by
  simpa only [hR] using
    matrixExp_unitary_conj ⟨R, reflection_mem_unitary R hR hR2⟩ A

/-- The trace exponential is invariant under a self-adjoint involution.
Source: trace cyclicity and reflection pinching, operator derivations §7;
atlas `golden-thompson` (helper). -/
theorem traceExp_reflection_conj (R A : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR2 : R * R = 1) :
    traceExp (R * A * R) = traceExp A := by
  simpa only [hR] using
    traceExp_unitary_conj ⟨R, reflection_mem_unitary R hR hR2⟩ A

/-- Positive definiteness is preserved and reflected by a self-adjoint involution.
Source: invertible quadratic-form congruence, Tropp 2015, §2.1.5;
atlas `golden-thompson` (helper). -/
theorem posDef_reflection_conj_iff (R A : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR2 : R * R = 1) :
    (R * A * R).PosDef ↔ A.PosDef := by
  simpa only [hR] using
    posDef_unitary_conj_iff ⟨R, reflection_mem_unitary R hR hR2⟩ A

/-- A reflection fixing the Lieb parameter preserves its trace function.
Source: the midpoint pinching argument in operator derivations §7;
atlas `golden-thompson` (helper). -/
theorem traceExp_add_matrixLog_reflection_conj_of_conj_eq (R H A : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR2 : R * R = 1) (hA : A.IsHermitian)
    (hH : R * H * R = H) :
    traceExp (H + matrixLog (R * A * R)) = traceExp (H + matrixLog A) := by
  simpa only [hR] using
    traceExp_add_matrixLog_unitary_conj_of_conj_eq
      ⟨R, reflection_mem_unitary R hR hR2⟩ H A hA (by simpa only [hR] using hH)

private def diagonalStarAlgHom : (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ :=
  { (Matrix.diagonalAlgHom ℂ : (ι → ℂ) →ₐ[ℂ] Matrix ι ι ℂ) with
    map_star' := by intro x; simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose] }

set_option backward.isDefEq.respectTransparency false in
/-- Real functional calculus acts entrywise on a real diagonal matrix.
Arbitrary real functions are allowed because the diagonal spectrum is finite.
Source: the private `cfc_diag` proof in `JointTensorRepresentation`, via Mathlib's
diagonal algebra homomorphism and Pi CFC; Tropp 2015, §2.1.11;
atlas `golden-thompson`, `operator-monotone-convex` (helper). -/
theorem cfc_diagonal_real (f : ℝ → ℝ) (x : ι → ℝ) :
    cfc f (Matrix.diagonal fun i => (x i : ℂ)) =
      Matrix.diagonal fun i => (f (x i) : ℂ) := by
  let := IsStarNormal.instContinuousFunctionalCalculus (A := ι → ℂ)
  let := IsSelfAdjoint.instContinuousFunctionalCalculus (A := ι → ℂ)
  let z : ι → ℂ := fun i => (x i : ℂ)
  have hx : IsSelfAdjoint z := by ext; simp [z]
  have hd : IsSelfAdjoint (diagonalStarAlgHom z) := hx.map diagonalStarAlgHom
  have hc : ContinuousOn f (spectrum ℝ z) := by
    rw [Pi.spectrum_eq]
    have heq : (⋃ i, spectrum ℝ (z i)) = Set.range x := by
      change (⋃ i, spectrum ℝ (algebraMap ℝ ℂ (x i))) = _
      simp only [spectrum.scalar_eq, Set.iUnion_singleton_eq_range]
    rw [heq]
    exact Set.Finite.continuousOn (Set.finite_range _) _
  have heq := diagonalStarAlgHom.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) f z hc
    (by change Continuous (fun z : ι → ℂ => Matrix.diagonal z); fun_prop) hx hd
  rw [cfc_map_pi (p := IsSelfAdjoint) (q := fun _ => IsSelfAdjoint) (S := ℂ) f z
    (by rwa [← Pi.spectrum_eq]) hx (fun i => by
      change star (x i : ℂ) = (x i : ℂ); simp)] at heq
  change Matrix.diagonal (fun i => cfc f (algebraMap ℝ ℂ (x i))) =
    cfc f (Matrix.diagonal fun i => (x i : ℂ)) at heq
  simp only [cfc_algebraMap] at heq
  exact heq.symm

omit [DecidableEq ι] in
/-- Equivalent finite labels preserve the complex trace. Source: the private
`trace_reindex` helper in `IntrinsicBernstein`, by reindexing the diagonal sum;
atlas `golden-thompson` (finite-index transport helper). -/
theorem trace_reindex {κ : Type*} [Fintype κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => A i i)

/-- Equivalent finite labels commute with the matrix exponential, with no
Hermitian premise. Source: continuous algebra-isomorphism transport of the
exponential; atlas `golden-thompson` (finite-index transport helper). -/
theorem matrixExp_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    matrixExp (Matrix.reindex e e A) = Matrix.reindex e e (matrixExp A) := by
  let E := reindexStarAlgEquiv e
  symm
  change E (NormedSpace.exp A) = NormedSpace.exp (E A)
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) E
    E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional A
    ((NormedSpace.expSeries_radius_eq_top ℂ (Matrix ι ι ℂ)).symm ▸ edist_lt_top _ _)

/-- Equivalent finite labels preserve the trace exponential, with no Hermitian
premise. Source: exponential transport and invariance of the diagonal sum;
atlas `golden-thompson` (finite-index transport helper). -/
theorem traceExp_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    traceExp (Matrix.reindex e e A) = traceExp A := by
  unfold traceExp
  rw [matrixExp_reindex, trace_reindex]

end NLAlib
