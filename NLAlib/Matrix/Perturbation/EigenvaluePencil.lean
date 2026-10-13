import NLAlib.Matrix.Perturbation.EigenvaluePerturbation
import NLAlib.Matrix.Spectral.SingularValueSpectrum

/-!
# Continuous signed eigenvalues of a symmetric affine pencil

Weyl's spectral Lipschitz inequality gives continuity of each sorted signed
eigenvalue of `A + t B`, without any assumption on multiplicities.
Source: Bhatia 1997, Section III.4; supports the compact-variation proof of `lidskii`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
omit [Fintype n] [DecidableEq n] in
/-- The symmetric affine pencil `A + t B` is Hermitian at every real parameter.
This proof-valued interface fixes the sorted eigenvalue witnesses used by Lidskii.
-/
theorem isHermitian_add_smul {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (t : ℝ) : (A + t • B).IsHermitian :=
  hA.add (hB.smul (by simp [IsSelfAdjoint]))

open scoped Matrix.Norms.L2Operator in
/-- Sorted signed eigenvalues of a symmetric affine pencil vary by at most
`|s-t| ‖B‖`. Weyl's bound, Horn–Johnson 2013, Corollary 4.3.15; no simple spectrum.
-/
theorem abs_eigenvalues₀_pencil_sub_le {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card n)) (s t : ℝ) :
    |(isHermitian_add_smul hA hB s).eigenvalues₀ i -
      (isHermitian_add_smul hA hB t).eigenvalues₀ i| ≤ |s - t| * specNorm B := by
  have h := abs_eigenvalues₀_sub_le_specNorm_sub
    (isHermitian_add_smul hA hB t) (isHermitian_add_smul hA hB s) i
  have hd : (A + s • B) - (A + t • B) = (s - t) • B := by
    rw [sub_smul]
    abel
  simpa only [hd, specNorm, norm_smul, Real.norm_eq_abs] using h

open scoped Matrix.Norms.L2Operator in
/-- Each decreasing signed eigenvalue of a real symmetric affine pencil is
Lipschitz with constant `‖B‖`. Weyl's perturbation theorem; Lidskii continuity step.
-/
theorem lipschitzWith_eigenvalues₀_pencil {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    LipschitzWith ⟨specNorm B, specNorm_nonneg B⟩
      (fun t : ℝ => (isHermitian_add_smul hA hB t).eigenvalues₀ i) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist _ _ ≤ specNorm B * dist s t
  simp only [Real.dist_eq]
  exact (abs_eigenvalues₀_pencil_sub_le hA hB i s t).trans_eq (mul_comm _ _)

open scoped Matrix.Norms.L2Operator in
/-- Sorted signed eigenvalues of a symmetric affine pencil are continuous,
including at eigenvalue crossings. Bhatia 1997, Section III.4, Lidskii proof.
-/
theorem continuous_eigenvalues₀_pencil {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    Continuous (fun t : ℝ => (isHermitian_add_smul hA hB t).eigenvalues₀ i) :=
  (lipschitzWith_eigenvalues₀_pencil hA hB i).continuous

/-- Successive increments of a symmetric affine pencil agree with their summed
parameter. The exact matrix identity; supports the shifted Lidskii variation.
-/
theorem eigenvalues₀_pencil_add {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (t h : ℝ) (i : Fin (Fintype.card n)) :
    (isHermitian_add_smul (isHermitian_add_smul hA hB t) hB h).eigenvalues₀ i =
      (isHermitian_add_smul hA hB (t + h)).eigenvalues₀ i := by
  refine congrFun (eigenvalues₀_eq_of_matrix_eq _ _ ?_) i
  rw [add_smul]
  abel

end NLAlib
