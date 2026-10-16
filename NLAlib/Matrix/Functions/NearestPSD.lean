import NLAlib.Matrix.Functions.CFCTrace
import NLAlib.Matrix.Basic.PSDDuality
import NLAlib.Matrix.Norms.Frobenius
/-!
# Frobenius projection onto a positive-semidefinite floor

The Hermitian part is orthogonal to the skew-Hermitian part in the real
Frobenius inner product. Clipping its eigenvalues at a real floor constructs
the unique Frobenius-nearest Hermitian matrix above that floor. Its normal
variational inequality also gives nonexpansiveness.

Source: Higham (1988), nearest positive semidefinite matrix theorem;
matrix-toolkit re-derivation, §33. Atlas: `nearest-psd-frobenius`.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian part of a finite matrix. -/
def matrixHermitianPart (A : Matrix n n 𝕜) : Matrix n n 𝕜 := (1 / 2 : ℝ) • (A + Aᴴ)

/-- The complementary skew-Hermitian part. -/
def matrixSkewHermitianPart (A : Matrix n n 𝕜) : Matrix n n 𝕜 := A - matrixHermitianPart A

/-- The Hermitian part is Hermitian over either scalar field. -/
theorem isHermitian_matrixHermitianPart (A : Matrix n n 𝕜) :
    (matrixHermitianPart A).IsHermitian := by
  ext i j
  simp [matrixHermitianPart, Matrix.conjTranspose_apply, RCLike.real_smul_eq_coe_mul,
    mul_add, add_comm]

/-- The complementary part changes sign under the adjoint. -/
theorem matrixSkewHermitianPart_conjTranspose (A : Matrix n n 𝕜) :
    (matrixSkewHermitianPart A)ᴴ = -matrixSkewHermitianPart A := by
  ext i j
  simp [matrixSkewHermitianPart, matrixHermitianPart, Matrix.conjTranspose_apply,
    RCLike.real_smul_eq_coe_mul]
  field_simp
  norm_num only [RCLike.ofReal_ofNat]
  ring

/-- Skew-Hermitian and Hermitian matrices are Frobenius orthogonal. -/
theorem frobInner_eq_zero_of_skewHermitian_of_isHermitian {K X : Matrix n n 𝕜}
    (hK : Kᴴ = -K) (hX : X.IsHermitian) : frobInner K X = 0 := by
  have he := frobInner_conjTranspose K X
  rw [hK, hX.eq, frobInner_neg_left] at he
  linarith

/-- Spectral clipping of a Hermitian matrix at a real floor. -/
def _root_.Matrix.IsHermitian.spectralClip {H : Matrix n n 𝕜} (hH : H.IsHermitian) (δ : ℝ) :
    Matrix n n 𝕜 := hH.cfc (fun t => max δ t)

/-- The Frobenius-nearest matrix above a scalar PSD floor. -/
def nearestPSD (A : Matrix n n 𝕜) (δ : ℝ) : Matrix n n 𝕜 :=
  (isHermitian_matrixHermitianPart A).spectralClip δ

/-- Clipping is feasible, its outward correction is PSD, and the correction
is complementary to the part strictly above the floor. -/
theorem _root_.Matrix.IsHermitian.spectralClip_properties {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (δ : ℝ) :
    (hH.spectralClip δ - δ • 1).PosSemidef ∧
      (hH.spectralClip δ - H).PosSemidef ∧
      (hH.spectralClip δ - H) * (hH.spectralClip δ - δ • 1) = 0 := by
  let U : Matrix n n 𝕜 := hH.eigenvectorUnitary
  let d := hH.eigenvalues
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hUU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hHrep : H = U * diagonal (fun i => (d i : 𝕜)) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      U, d, Function.comp_def] using hH.spectral_theorem
  have hPrep : hH.spectralClip δ = U * diagonal (fun i => ((max δ (d i) : ℝ) : 𝕜)) * Uᴴ :=
    cfc_eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose hH _
  have hshift : hH.spectralClip δ - δ • 1 =
      U * diagonal (fun i => (max δ (d i) - δ : 𝕜)) * Uᴴ := by
    rw [hPrep, ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    rw [show diagonal (fun _ : n => (δ : 𝕜)) = δ • (1 : Matrix n n 𝕜) by
      ext i j; by_cases hij : i = j <;> simp [hij, RCLike.real_smul_eq_coe_mul]]
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU]
  have hcorrection : hH.spectralClip δ - H =
      U * diagonal (fun i => (max δ (d i) - d i : 𝕜)) * Uᴴ := by
    rw [hPrep, hHrep, ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
  have hp1 : (diagonal (fun i => (max δ (d i) - δ : 𝕜))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact sub_nonneg.mpr (by exact_mod_cast le_max_left δ (d i))
  have hp2 : (diagonal (fun i => (max δ (d i) - d i : 𝕜))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact sub_nonneg.mpr (by exact_mod_cast le_max_right δ (d i))
  refine ⟨hshift ▸ hp1.mul_mul_conjTranspose_same U,
    hcorrection ▸ hp2.mul_mul_conjTranspose_same U, ?_⟩
  rw [hshift, hcorrection]
  calc
    _ = U * ((diagonal fun i => (max δ (d i) - d i : 𝕜)) *
        (Uᴴ * U) * diagonal (fun i => (max δ (d i) - δ : 𝕜))) * Uᴴ := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by
      rw [hU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
      have hz : (diagonal fun i => (max δ (d i) - d i : 𝕜) * (max δ (d i) - δ)) = 0 := by
        ext i j
        by_cases hij : i = j
        · subst j
          rcases le_total δ (d i) with hi | hi <;> simp [max_eq_left hi, max_eq_right hi]
        · simp [hij]
      rw [hz, Matrix.mul_zero, Matrix.zero_mul]

/-- The spectral clip is Hermitian. -/
theorem _root_.Matrix.IsHermitian.isHermitian_spectralClip {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (δ : ℝ) : (hH.spectralClip δ).IsHermitian := by
  have hp := (hH.spectralClip_properties δ).2.1.isHermitian
  have he : hH.spectralClip δ = (hH.spectralClip δ - H) + H := by abel
  rw [he]
  exact hp.add hH

/-- The normal-cone variational inequality characterizing the clipped
projection, for arbitrary input matrices and real PSD floor. -/
theorem frobInner_sub_nearestPSD_le_zero (A : Matrix n n 𝕜) (δ : ℝ)
    {X : Matrix n n 𝕜} (hX : X.IsHermitian) (hfloor : (X - δ • 1).PosSemidef) :
    frobInner (A - nearestPSD A δ) (X - nearestPSD A δ) ≤ 0 := by
  let H := matrixHermitianPart A
  let hH := isHermitian_matrixHermitianPart A
  let P := nearestPSD A δ
  have hP : P.IsHermitian := hH.isHermitian_spectralClip δ
  have hR : (P - H).PosSemidef := (hH.spectralClip_properties δ).2.1
  have hcomp : (P - H) * (P - δ • 1) = 0 := (hH.spectralClip_properties δ).2.2
  have htrace : 0 ≤ frobInner (P - H) (X - δ • 1) := by
    rw [frobInner_eq_trace, hR.isHermitian.eq]
    exact (RCLike.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef hR hfloor)).1
  have hzero : frobInner (P - H) (P - δ • 1) = 0 := by
    rw [frobInner_eq_trace, hR.isHermitian.eq, hcomp, Matrix.trace_zero, map_zero]
  have hskew : frobInner (A - H) (X - P) = 0 :=
    frobInner_eq_zero_of_skewHermitian_of_isHermitian (matrixSkewHermitianPart_conjTranspose A)
      (hX.sub hP)
  have hsplit : A - P = (A - H) - (P - H) := by abel
  change frobInner (A - P) (X - P) ≤ 0
  rw [hsplit, frobInner_sub_left, hskew]
  have he : frobInner (P - H) (X - P) =
      frobInner (P - H) (X - δ • 1) - frobInner (P - H) (P - δ • 1) := by
    rw [← frobInner_sub_right]
    congr 1
    abel
  rw [he, hzero]
  linarith

/-- Spectral clipping is the unique Frobenius nearest feasible matrix.
The strict comparison includes arbitrary non-Hermitian inputs.
atlas: nearest-psd-frobenius (partial) -/
theorem nearestPSD_unique_minimizer (A : Matrix n n 𝕜) (δ : ℝ) :
    (nearestPSD A δ).IsHermitian ∧ (nearestPSD A δ - δ • 1).PosSemidef ∧
      ∀ X : Matrix n n 𝕜, X.IsHermitian → (X - δ • 1).PosSemidef →
        frobSq (A - nearestPSD A δ) ≤ frobSq (A - X) ∧
          (frobSq (A - X) ≤ frobSq (A - nearestPSD A δ) → X = nearestPSD A δ) := by
  refine ⟨(isHermitian_matrixHermitianPart A).isHermitian_spectralClip δ,
    ((isHermitian_matrixHermitianPart A).spectralClip_properties δ).1, ?_⟩
  intro X hX hfloor
  have hv := frobInner_sub_nearestPSD_le_zero A δ hX hfloor
  have he : A - X = (A - nearestPSD A δ) - (X - nearestPSD A δ) := by abel
  have hdiff : frobSq (A - X) = frobSq (A - nearestPSD A δ) -
      2 * frobInner (A - nearestPSD A δ) (X - nearestPSD A δ) +
        frobSq (X - nearestPSD A δ) := by rw [he, frobSq_sub]
  have hn := frobSq_nonneg (X - nearestPSD A δ)
  constructor
  · linarith
  · intro hle
    have hz : frobSq (X - nearestPSD A δ) = 0 := by linarith
    exact sub_eq_zero.mp ((frobSq_eq_zero_iff _).mp hz)

/-- Spectral clipping is nonexpansive in Frobenius norm. The proof uses
the normal inequalities at both inputs, so no spectral-norm assertion or
commutativity between the two input matrices is needed.
atlas: nearest-psd-frobenius (partial) -/
theorem frobNorm_nearestPSD_sub_le (A B : Matrix n n 𝕜) (δ : ℝ) :
    frobNorm (nearestPSD A δ - nearestPSD B δ) ≤ frobNorm (A - B) := by
  let P := nearestPSD A δ
  let Q := nearestPSD B δ
  have hp := nearestPSD_unique_minimizer A δ
  have hq := nearestPSD_unique_minimizer B δ
  have hv1 := frobInner_sub_nearestPSD_le_zero A δ hq.1 hq.2.1
  have hv2 := frobInner_sub_nearestPSD_le_zero B δ hp.1 hp.2.1
  have hpair : frobSq (P - Q) ≤ frobInner (A - B) (P - Q) := by
    change frobInner (A - P) (Q - P) ≤ 0 at hv1
    change frobInner (B - Q) (P - Q) ≤ 0 at hv2
    have hrev : Q - P = -(P - Q) := by abel
    rw [hrev, frobInner_neg_right] at hv1
    have he : frobInner (A - B) (P - Q) - frobSq (P - Q) =
        frobInner (A - P) (P - Q) - frobInner (B - Q) (P - Q) := by
      simp only [frobInner_sub_left, frobSq]
      ring
    linarith
  have hCS := frobInner_le_frobNorm_mul_frobNorm (A - B) (P - Q)
  have hsq := frobNorm_sq (P - Q)
  have hn := frobNorm_nonneg (P - Q)
  have hm := frobNorm_nonneg (A - B)
  change frobNorm (P - Q) ≤ _
  nlinarith

/-- The squared size of the clipping correction is the sum of squared
eigenvalue deficits below the floor. -/
theorem _root_.Matrix.IsHermitian.frobSq_spectralClip_sub {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (δ : ℝ) :
    frobSq (hH.spectralClip δ - H) =
      ∑ i, max (δ - hH.eigenvalues i) 0 ^ 2 := by
  let U : Matrix n n 𝕜 := hH.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hHrep : H = U * diagonal (fun i => (hH.eigenvalues i : 𝕜)) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      U, Function.comp_def] using hH.spectral_theorem
  have hPrep : hH.spectralClip δ =
      U * diagonal (fun i => ((max δ (hH.eigenvalues i) : ℝ) : 𝕜)) * Uᴴ :=
    cfc_eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose hH _
  have he : hH.spectralClip δ - H =
      U * diagonal (fun i => ((max δ (hH.eigenvalues i) - hH.eigenvalues i : ℝ) : 𝕜)) * Uᴴ := by
    calc
      _ = U * diagonal (fun i => ((max δ (hH.eigenvalues i) : ℝ) : 𝕜)) * Uᴴ -
          U * diagonal (fun i => (hH.eigenvalues i : 𝕜)) * Uᴴ :=
        congrArg₂ (· - ·) hPrep hHrep
      _ = _ := by
        simp only [RCLike.ofReal_sub, ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
  rw [he, frobSq_mul_right_of_orthonormal hU, frobSq_mul_left_of_orthonormal hU,
    frobSq_diagonal]
  apply Finset.sum_congr rfl
  intro i hi
  rw [RCLike.norm_ofReal, abs_of_nonneg (sub_nonneg.mpr (le_max_right δ (hH.eigenvalues i)))]
  congr 1
  rcases le_total δ (hH.eigenvalues i) with hle | hle
  · rw [max_eq_right hle, sub_self, max_eq_right (sub_nonpos.mpr hle)]
  · rw [max_eq_left hle, max_eq_left (sub_nonneg.mpr hle)]

/-- The exact minimum squared Frobenius distance is the skew-Hermitian
energy plus the squared deficits of Hermitian eigenvalues below the floor.
Together with uniqueness and nonexpansiveness, this is the full nearest-PSD
formula for arbitrary input matrices.
atlas: nearest-psd-frobenius (partial) -/
theorem frobSq_sub_nearestPSD_eq (A : Matrix n n 𝕜) (δ : ℝ) :
    frobSq (A - nearestPSD A δ) = frobSq (matrixSkewHermitianPart A) +
      ∑ i, max (δ - (isHermitian_matrixHermitianPart A).eigenvalues i) 0 ^ 2 := by
  let H := matrixHermitianPart A
  let hH := isHermitian_matrixHermitianPart A
  have hP := hH.isHermitian_spectralClip δ
  have he : A - nearestPSD A δ = matrixSkewHermitianPart A - (nearestPSD A δ - H) := by
    dsimp [matrixSkewHermitianPart, H]
    abel
  have horth : frobInner (matrixSkewHermitianPart A) (nearestPSD A δ - H) = 0 :=
    frobInner_eq_zero_of_skewHermitian_of_isHermitian (matrixSkewHermitianPart_conjTranspose A)
      (hP.sub hH)
  rw [he, frobSq_sub_of_frobInner_eq_zero _ _ horth]
  exact congrArg (fun q => frobSq (matrixSkewHermitianPart A) + q)
    (hH.frobSq_spectralClip_sub δ)

end NLAlib
