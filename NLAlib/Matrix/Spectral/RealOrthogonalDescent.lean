import NLAlib.Matrix.Spectral.RealSimilarityDescent
import NLAlib.Matrix.Factorizations.PolarIntertwining
/-!
# Descending unitary similarities to real orthogonal similarities

One determinant-pencil intertwiner is chosen for the original real families
and their transposes together. Its real polar frame is one common orthogonal
similarity. Source: Horn–Johnson (2013), Theorem 2.5.21;
atlas `real-similarity-descent`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- A common complex unitary similarity between real families descends to
one common real orthogonal similarity. Source: Horn–Johnson (2013),
Theorem 2.5.21; arbitrary family indices and empty matrix shapes are included.
atlas: real-similarity-descent (partial) -/
theorem exists_real_orthogonal_similarity_of_complex_unitary_similarity
    (A B : ι → Matrix n n ℝ) (U : Matrix.unitaryGroup n ℂ)
    (hAB : ∀ i, (A i).map Complex.ofReal =
      (U : Matrix n n ℂ) * (B i).map Complex.ofReal * (U : Matrix n n ℂ)ᴴ) :
    ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧ ∀ i, A i = Q * B i * Qᵀ := by
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hUUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have hmap (M : Matrix n n ℝ) :
      (M.map Complex.ofReal)ᴴ = Mᵀ.map Complex.ofReal := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply,
      Complex.star_def, Complex.conj_ofReal]
  have hinter (i : ι) : (A i).map Complex.ofReal * (U : Matrix n n ℂ) =
      (U : Matrix n n ℂ) * (B i).map Complex.ofReal := by
    rw [hAB i, Matrix.mul_assoc, hUUt, Matrix.mul_one]
  have hAdj (i : ι) : (A i)ᵀ.map Complex.ofReal * (U : Matrix n n ℂ) =
      (U : Matrix n n ℂ) * (B i)ᵀ.map Complex.ofReal := by
    have hsim : ((A i).map Complex.ofReal)ᴴ =
        (U : Matrix n n ℂ) * ((B i).map Complex.ofReal)ᴴ * (U : Matrix n n ℂ)ᴴ := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc] using congrArg Matrix.conjTranspose (hAB i)
    rw [← hmap, ← hmap, hsim, Matrix.mul_assoc, hUUt, Matrix.mul_one]
  let A' : Sum ι ι → Matrix n n ℝ := Sum.elim A (fun i => (A i)ᵀ)
  let B' : Sum ι ι → Matrix n n ℝ := Sum.elim B (fun i => (B i)ᵀ)
  have hfamily (k : Sum ι ι) : (A' k).map Complex.ofReal * (U : Matrix n n ℂ) =
      (U : Matrix n n ℂ) * (B' k).map Complex.ofReal := by
    cases k with
    | inl i => exact hinter i
    | inr i => exact hAdj i
  obtain ⟨T, hT, hAT⟩ := exists_real_isUnit_intertwiner_of_complex
    (Unitary.isUnit_coe (U := U)) hfamily
  have hTt : IsUnit Tᵀ := Tᵀ.isUnit_iff_isUnit_det.mpr
    (by simpa only [Matrix.det_transpose] using T.isUnit_iff_isUnit_det.mp hT)
  have hGram : IsUnit (Tᵀ * T) := hTt.mul hT
  let Q := polarFrame T
  have hQ : HasOrthonormalCols Q := hasOrthonormalCols_polarFrame T hGram
  have hQt : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  refine ⟨Q, hQ, fun i => ?_⟩
  have hAQ : A i * Q = Q * B i :=
    mul_polarFrame_eq_polarFrame_mul_of_intertwining (A i) (B i) T hGram
      (hAT (Sum.inl i)) (hAT (Sum.inr i))
  calc
    A i = A i * (Q * Qᵀ) := by rw [hQt, Matrix.mul_one]
    _ = Q * B i * Qᵀ := by rw [← Matrix.mul_assoc, hAQ]

/-- Both real-descent clauses with their common-family quantifiers:
nonsingular complex similarities descend to nonsingular real similarities,
and unitary complex similarities descend to real orthogonal similarities.
Source: Horn–Johnson (2013), Theorems 1.3.29 and 2.5.21.
atlas: real-similarity-descent -/
theorem real_similarity_descent_properties (A B : ι → Matrix n n ℝ) :
    (∀ S : Matrix n n ℂ, IsUnit S →
      (∀ i, (A i).map Complex.ofReal = S * (B i).map Complex.ofReal * S⁻¹) →
      ∃ T : Matrix n n ℝ, IsUnit T ∧ ∀ i, A i = T * B i * T⁻¹) ∧
    (∀ U : Matrix.unitaryGroup n ℂ,
      (∀ i, (A i).map Complex.ofReal =
        (U : Matrix n n ℂ) * (B i).map Complex.ofReal * (U : Matrix n n ℂ)ᴴ) →
      ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧ ∀ i, A i = Q * B i * Qᵀ) :=
  ⟨fun _ hS hAB => exists_real_similarity_of_complex_similarity hS hAB,
    fun U hAB => exists_real_orthogonal_similarity_of_complex_unitary_similarity A B U hAB⟩

end NLAlib
