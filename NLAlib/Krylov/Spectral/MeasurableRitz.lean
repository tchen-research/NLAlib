import NLAlib.Krylov.Spaces.Polynomial
import NLAlib.Matrix.Spectral.PowerRayleigh
import NLAlib.Matrix.Subspaces.OrthonormalBasisMatrix
import NLAlib.Matrix.Functions.CFCQuadratic
import NLAlib.Matrix.Spectral.EigenvalueEquality
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Ritz values of an orthonormal compression

Ritz values are the sorted eigenvalues of `Qᴴ A Q`, where the orthonormal columns of `Q`
span the trial space. The canonical Krylov compression uses exactly `dim K_q(A,b)` columns,
including early breakdown. Its largest Ritz value is zero for the trivial space. Variational
suprema below exclude the zero vector and serve as bridges and measurability proofs.

Source: Parlett (1998), Thm 11.4.1; Kuczyński–Woźniakowski (1992), §2.
-/

noncomputable section
open scoped Matrix
open MeasureTheory
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The sorted Ritz values of the Hermitian compression to an orthonormal frame.
The columns of `Q` are a basis for `range Q`; a zero-column frame has no Ritz values.
Source: Parlett (1998), Thm 11.4.1. -/
def ritzValues {𝕜 : Type*} [RCLike 𝕜] {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (Q : Matrix n r 𝕜)
    (_hQ : HasOrthonormalCols Q) : Fin (Fintype.card r) → ℝ :=
  (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues₀

/-- The largest eigenvalue of the canonical orthonormal Krylov compression.
Its dimension is `dim K_q(A,b)`, so breakdown never pads the spectrum with zero.
The trivial Krylov space and non-Hermitian matrices have the declared value zero.
Source: Parlett (1998), Thm 11.4.1; Kuczyński–Woźniakowski (1992), §2.
atlas: random-start-power -/
def lanczosRitzValue (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) : ℝ :=
  if hA : A.IsHermitian then
    if hd : 0 < Module.finrank ℝ (krylovSpace A b q) then
      ritzValues hA (orthonormalBasisMatrix (krylovSpace A b q))
        (hasOrthonormalCols_orthonormalBasisMatrix _) ⟨0, by simpa using hd⟩
    else 0
  else 0

/-- A Krylov vector specified by coefficients in its generating sequence. -/
def krylovCoefficientVector {K : Type*} [Field K] (A : Matrix n n K) (b : n → K) {q : ℕ}
    (c : Fin q → K) : n → K := ∑ j : Fin q, c j • ((A ^ (j : ℕ)) *ᵥ b)

/-- The coefficient representation of a Krylov space, including zero generators. -/
theorem mem_krylovSpace_iff_exists_coefficients {K : Type*} [Field K]
    (A : Matrix n n K) (b : n → K) (q : ℕ) (y : n → K) :
    y ∈ krylovSpace A b q ↔ ∃ c : Fin q → K, krylovCoefficientVector A b c = y := by
  exact Submodule.mem_span_range_iff_exists_fun K

/-- Every linear combination of Krylov generators lies in the Krylov space. -/
theorem krylovCoefficientVector_mem {K : Type*} [Field K] (A : Matrix n n K)
    (b : n → K) {q : ℕ} (c : Fin q → K) :
    krylovCoefficientVector A b c ∈ krylovSpace A b q :=
  (mem_krylovSpace_iff_exists_coefficients A b q _).mpr ⟨c, rfl⟩

omit [DecidableEq n] in
/-- The real Rayleigh quotient as a quotient of dot products. Helper. -/
theorem rayleighQuotient_eq_div (A : Matrix n n ℝ) (x : n → ℝ) :
    rayleighQuotient A x = x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x) := by
  rw [rayleighQuotient_def, quadForm_def, star_trivial, RCLike.re_to_real, RCLike.re_to_real]

/-- A Rayleigh quotient is at most the spectral norm: `xᵀAx/xᵀx ≤ ‖A‖₂` (any real `A`, including
`x = 0`). Helper for `random-start-lanczos`. -/
theorem rayleighQuotient_le_specNorm (A : Matrix n n ℝ) (x : n → ℝ) :
    rayleighQuotient A x ≤ specNorm A := by
  rw [rayleighQuotient_eq_div]
  rcases eq_or_lt_of_le (dotProduct_self_nonneg x) with h0 | hpos
  · rw [← h0, div_zero]; exact specNorm_nonneg A
  · rw [div_le_iff₀ hpos]
    have h := abs_re_star_dotProduct_mulVec_le_specNorm A x
    rw [star_trivial, RCLike.re_to_real, norm_toLp_sq_eq_dotProduct_self] at h
    exact (le_abs_self _).trans h

private lemma dotProduct_self_pos_of_ne_zero {r : Type*} [Fintype r]
    {z : r → ℝ} (hz : z ≠ 0) : 0 < z ⬝ᵥ z :=
  lt_of_le_of_ne (dotProduct_self_nonneg _)
    (Ne.symm fun h => hz (dotProduct_self_eq_zero.mp h))

omit [DecidableEq n] in
/-- Rayleigh quotients are preserved by an orthonormal compression. -/
theorem rayleighQuotient_compression {r : Type*} [Fintype r] [DecidableEq r]
    (A : Matrix n n ℝ) {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q) (z : r → ℝ) :
    rayleighQuotient (Qᴴ * A * Q) z = rayleighQuotient A (Q *ᵥ z) := by
  rw [rayleighQuotient_eq_div, rayleighQuotient_eq_div]
  have hd := star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ z
  simp only [star_trivial] at hd
  rw [hd]
  congr 1
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec z Qᵀ, Matrix.vecMul_transpose]

/-- The largest compression eigenvalue is the supremum over nonzero trial vectors.
The empty frame gives the supremum of the empty set, namely zero.
Source: Parlett (1998), Thm 11.4.1. -/
theorem lambdaMax_compression_eq_sSup_rayleigh {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {Q : Matrix n r ℝ}
    (hQ : HasOrthonormalCols Q) :
    lambdaMax (Qᴴ * A * Q) =
      sSup (rayleighQuotient A '' {x | x ∈ LinearMap.range Q.mulVecLin ∧ x ≠ 0}) := by
  let hT := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  cases isEmpty_or_nonempty r with
  | inl hr =>
    let := hr
    have he : {x : n → ℝ | x ∈ LinearMap.range Q.mulVecLin ∧ x ≠ 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨z, rfl⟩ hz
      apply hz
      ext i
      simp [Matrix.mulVec, dotProduct]
    rw [he, Set.image_empty, Real.sSup_empty, lambdaMax, hT.spectrum_real_eq_range_eigenvalues]
    rw [Set.range_eq_empty]
    exact Real.sSup_empty
  | inr hr =>
    let := hr
    let L := hT.eigenvalues₀ ⟨0, Fintype.card_pos⟩
    have hbound : ∀ z : r → ℝ, z ≠ 0 → rayleighQuotient (Qᴴ * A * Q) z ≤ L := by
      intro z hz
      rw [rayleighQuotient_eq_div, div_le_iff₀ (dotProduct_self_pos_of_ne_zero hz)]
      exact dotProduct_mulVec_le_mul_dotProduct_of_eigenvalues hT
        (fun j => hT.eigenvalues₀_antitone (Nat.zero_le _)) z
    have hmax : ∃ z : r → ℝ, z ≠ 0 ∧ rayleighQuotient (Qᴴ * A * Q) z = L := by
      let i := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card r))
        (⟨0, Fintype.card_pos⟩ : Fin (Fintype.card r))
      let z : r → ℝ := hT.eigenvectorBasis i
      have hz : z ≠ 0 := by
        intro hz
        have hn := (hT.eigenvectorBasis).norm_eq_one i
        change ‖WithLp.toLp 2 z‖ = 1 at hn
        simp [hz] at hn
      refine ⟨z, hz, ?_⟩
      rw [rayleighQuotient_eq_div, hT.mulVec_eigenvectorBasis, dotProduct_smul, smul_eq_mul]
      rw [mul_div_cancel_right₀ _ (dotProduct_self_pos_of_ne_zero hz).ne']
      simp [Matrix.IsHermitian.eigenvalues, i, L]
    have hQinj : ∀ z : r → ℝ, Q *ᵥ z = 0 → z = 0 := by
      intro z hz
      have hd := star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ z
      simp only [star_trivial, hz, dotProduct_zero] at hd
      exact dotProduct_self_eq_zero.mp hd.symm
    rw [lambdaMax_eq_eigenvalues₀_zero hT]
    symm
    apply IsGreatest.csSup_eq
    constructor
    · obtain ⟨z, hz, hL⟩ := hmax
      refine ⟨Q *ᵥ z, ⟨⟨z, rfl⟩, fun h => hz (hQinj z h)⟩, ?_⟩
      exact (rayleighQuotient_compression A hQ z).symm.trans hL
    · rintro _ ⟨x, ⟨⟨z, rfl⟩, hx⟩, rfl⟩
      simp only [Matrix.mulVecLin_apply]
      rw [← rayleighQuotient_compression A hQ]
      exact hbound z (fun hz => hx (by simp [hz]))

omit [DecidableEq n] in
/-- Changing the orthonormal basis of a trial space preserves the entire ordered Ritz
spectrum, including multiplicities and empty spaces. Source: Parlett (1998), Thm 11.4.1. -/
theorem ritzValues_eq_of_range_eq {𝕜 : Type*} [RCLike 𝕜] {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q P : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) (hP : HasOrthonormalCols P)
    (hspan : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin) :
    ritzValues hA Q hQ = ritzValues hA P hP := by
  let U := Qᴴ * P
  have hQU : Q * U = P := mul_conjTranspose_mul_eq_of_range_le hQ hspan.ge
  have hUU : Uᴴ * U = 1 := by
    have hgram : (Q * U)ᴴ * (Q * U) = Uᴴ * U := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ Q,
        hQ.conjTranspose_mul_self, Matrix.one_mul]
    rw [hQU, hP.conjTranspose_mul_self] at hgram
    exact hgram.symm
  have hUt : U * Uᴴ = 1 := mul_eq_one_comm.mp hUU
  apply eigenvalues₀_eq_of_charpoly_eq
  have hc : Pᴴ * A * P = Uᴴ * (Qᴴ * A * Q) * U := by
    rw [← hQU, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hc, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc U Uᴴ, hUt, Matrix.one_mul]

/-- The largest Ritz value depends only on the spanned space, not the chosen orthonormal basis.
Source: Parlett (1998), Thm 11.4.1. -/
theorem lambdaMax_compression_eq_of_range_eq {r s : Type*} [Fintype r] [Fintype s]
    [DecidableEq r] [DecidableEq s] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : Matrix n r ℝ} {P : Matrix n s ℝ} (hQ : HasOrthonormalCols Q)
    (hP : HasOrthonormalCols P) (hspan : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin) :
    lambdaMax (Qᴴ * A * Q) = lambdaMax (Pᴴ * A * P) := by
  rw [lambdaMax_compression_eq_sSup_rayleigh hA hQ,
    lambdaMax_compression_eq_sSup_rayleigh hA hP, hspan]

/-- The canonical largest Krylov Ritz value is the extreme eigenvalue of its compression. -/
theorem lanczosRitzValue_eq_lambdaMax {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (b : n → ℝ) (q : ℕ) :
    lanczosRitzValue A b q = lambdaMax
      ((orthonormalBasisMatrix (krylovSpace A b q))ᴴ * A * orthonormalBasisMatrix (krylovSpace A b q)) := by
  unfold lanczosRitzValue
  rw [dif_pos hA]
  split_ifs with hd
  · letI : Nonempty (Fin (Module.finrank ℝ (krylovSpace A b q))) := Fin.pos_iff_nonempty.mp hd
    exact (lambdaMax_eq_eigenvalues₀_zero
      (Matrix.isHermitian_conjTranspose_mul_mul _ hA)).symm
  · have hd0 : Module.finrank ℝ (krylovSpace A b q) = 0 := by omega
    rw [lambdaMax, (Matrix.isHermitian_conjTranspose_mul_mul _ hA).spectrum_real_eq_range_eigenvalues]
    have : IsEmpty (Fin (Module.finrank ℝ (krylovSpace A b q))) := by rw [hd0]; infer_instance
    simp only [Set.range_eq_empty, Real.sSup_empty]

/-- The variational bridge for the largest Krylov Ritz value excludes the zero vector.
Source: Parlett (1998), Thm 11.4.1. -/
theorem lanczosRitzValue_eq_sSup_rayleigh {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (b : n → ℝ) (q : ℕ) :
    lanczosRitzValue A b q = sSup
      (rayleighQuotient A '' {x | x ∈ krylovSpace A b q ∧ x ≠ 0}) := by
  rw [lanczosRitzValue_eq_lambdaMax hA, lambdaMax_compression_eq_sSup_rayleigh hA
    (hasOrthonormalCols_orthonormalBasisMatrix _), range_orthonormalBasisMatrix]

/-- Any orthonormal basis spanning the Krylov space gives its largest Ritz value.
The nonempty frame condition ensures there is a largest eigenvalue.
Source: Parlett (1998), Thm 11.4.1. -/
theorem lanczosRitzValue_eq_ritzValues {r : Type*} [Fintype r] [DecidableEq r] [Nonempty r]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ) (q : ℕ)
    {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q)
    (hspan : LinearMap.range Q.mulVecLin = krylovSpace A b q) :
    lanczosRitzValue A b q = ritzValues hA Q hQ ⟨0, Fintype.card_pos⟩ := by
  rw [lanczosRitzValue_eq_lambdaMax hA]
  have he : LinearMap.range (orthonormalBasisMatrix (krylovSpace A b q)).mulVecLin =
      LinearMap.range Q.mulVecLin := (range_orthonormalBasisMatrix _).trans hspan.symm
  rw [lambdaMax_compression_eq_of_range_eq hA (hasOrthonormalCols_orthonormalBasisMatrix _) hQ he]
  exact lambdaMax_eq_eigenvalues₀_zero (Matrix.isHermitian_conjTranspose_mul_mul Q hA)

private lemma bddAbove_image (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    BddAbove (rayleighQuotient A '' {x | x ∈ krylovSpace A b q ∧ x ≠ 0}) :=
  ⟨specNorm A, by rintro _ ⟨y, _, rfl⟩; exact rayleighQuotient_le_specNorm A y⟩

/-- Every nonzero Krylov vector has quotient at most the largest compression eigenvalue. -/
theorem rayleighQuotient_le_lanczosRitzValue_of_mem_ne_zero {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (b : n → ℝ) (q : ℕ) {y : n → ℝ}
    (hy : y ∈ krylovSpace A b q) (hy0 : y ≠ 0) :
    rayleighQuotient A y ≤ lanczosRitzValue A b q := by
  rw [lanczosRitzValue_eq_sSup_rayleigh hA]
  exact le_csSup (bddAbove_image A b q) ⟨y, ⟨hy, hy0⟩, rfl⟩

/-- The largest Krylov Ritz value of a PSD matrix is nonnegative. -/
theorem lanczosRitzValue_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (b : n → ℝ) (q : ℕ) : 0 ≤ lanczosRitzValue A b q := by
  rw [lanczosRitzValue_eq_sSup_rayleigh hA.isHermitian]
  apply Real.sSup_nonneg
  rintro _ ⟨x, _, rfl⟩
  rw [rayleighQuotient_eq_div]
  exact div_nonneg (by simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg x)
    (dotProduct_self_nonneg _)

/-- For PSD matrices, the quotient inequality also holds at the zero vector. -/
theorem rayleighQuotient_le_lanczosRitzValue_of_mem {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (b : n → ℝ) (q : ℕ) {y : n → ℝ}
    (hy : y ∈ krylovSpace A b q) : rayleighQuotient A y ≤ lanczosRitzValue A b q := by
  by_cases hy0 : y = 0
  · simpa [hy0, rayleighQuotient_eq_div] using lanczosRitzValue_nonneg hA b q
  · exact rayleighQuotient_le_lanczosRitzValue_of_mem_ne_zero hA.isHermitian b q hy hy0

/-- The largest Krylov Ritz value is bounded by the spectral norm. -/
theorem lanczosRitzValue_le_specNorm (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    lanczosRitzValue A b q ≤ specNorm A := by
  by_cases hA : A.IsHermitian
  · rw [lanczosRitzValue_eq_sSup_rayleigh hA]
    apply Real.sSup_le _ (specNorm_nonneg A)
    rintro _ ⟨x, _, rfl⟩
    exact rayleighQuotient_le_specNorm A x
  · unfold lanczosRitzValue
    rw [dif_neg hA]
    exact specNorm_nonneg A

/-- The trivial Krylov space has largest Ritz value zero. -/
theorem lanczosRitzValue_eq_zero_of_space_eq_bot (A : Matrix n n ℝ) (b : n → ℝ)
    (q : ℕ) (h : krylovSpace A b q = ⊥) : lanczosRitzValue A b q = 0 := by
  simp [lanczosRitzValue, h]

/-- A rational-coefficient expression for the largest Ritz value. Zero coefficient images are
replaced by the starting quotient, which belongs to the same nonzero domain when the start is
nonzero and `q > 0`. Thus negative Ritz values are retained.
Source: Kuczyński–Woźniakowski (1992), §2 (variational form) and rational density. -/
theorem lanczosRitzValue_eq_iSup_rat {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (b : n → ℝ) (q : ℕ) :
    lanczosRitzValue A b q = if q = 0 then 0 else ⨆ c : Fin q → ℚ,
      let v := krylovCoefficientVector A b (fun j => (c j : ℝ))
      if v = 0 then rayleighQuotient A b else rayleighQuotient A v := by
  classical
  cases q with
  | zero => simp [lanczosRitzValue, krylovSpace_zero]
  | succ q =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    by_cases hb : b = 0
    · subst b
      simp [lanczosRitzValue, krylovCoefficientVector, rayleighQuotient_eq_div]
    let f := fun c : Fin (q + 1) → ℚ =>
      let v := krylovCoefficientVector A b (fun j => (c j : ℝ))
      if v = 0 then rayleighQuotient A b else rayleighQuotient A v
    have hB : BddAbove (Set.range f) := by
      refine ⟨specNorm A, ?_⟩
      rintro _ ⟨c, rfl⟩
      dsimp only [f]
      split_ifs <;> exact rayleighQuotient_le_specNorm A _
    let θ := ⨆ c, f c
    apply le_antisymm
    · rw [lanczosRitzValue_eq_sSup_rayleigh hA]
      refine csSup_le ⟨_, b, ⟨self_mem_krylovSpace_succ A b q, hb⟩, rfl⟩ ?_
      rintro _ ⟨y, ⟨hy, hy0⟩, rfl⟩
      have hRat : ∀ c : Fin (q + 1) → ℚ,
          let v := krylovCoefficientVector A b (fun j => (c j : ℝ))
          v ⬝ᵥ (A *ᵥ v) ≤ θ * (v ⬝ᵥ v) := by
        intro c
        dsimp only
        let v := krylovCoefficientVector A b (fun j => (c j : ℝ))
        by_cases hv : v = 0
        · change v ⬝ᵥ (A *ᵥ v) ≤ θ * (v ⬝ᵥ v)
          simp [hv]
        · have h := le_ciSup hB c
          change f c ≤ θ at h
          simp only [f, show krylovCoefficientVector A b (fun j => (c j : ℝ)) ≠ 0 from hv,
            ↓reduceIte, rayleighQuotient_eq_div] at h
          exact (div_le_iff₀ (dotProduct_self_pos_of_ne_zero hv)).mp h
      have hDense : DenseRange (fun c : Fin (q + 1) → ℚ => fun j => (c j : ℝ)) :=
        DenseRange.piMap (fun _ => Rat.denseRange_cast)
      obtain ⟨c, hc⟩ := (mem_krylovSpace_iff_exists_coefficients A b _ y).mp hy
      have hAll : (krylovCoefficientVector A b c) ⬝ᵥ (A *ᵥ krylovCoefficientVector A b c) ≤
          θ * (krylovCoefficientVector A b c ⬝ᵥ krylovCoefficientVector A b c) := by
        refine hDense.induction_on (p := fun c =>
          (krylovCoefficientVector A b c) ⬝ᵥ (A *ᵥ krylovCoefficientVector A b c) ≤
            θ * (krylovCoefficientVector A b c ⬝ᵥ krylovCoefficientVector A b c)) c ?_ hRat
        apply isClosed_le
        · simp only [krylovCoefficientVector, Matrix.mulVec, dotProduct, Finset.sum_apply,
            Pi.smul_apply, smul_eq_mul]
          fun_prop
        · simp only [krylovCoefficientVector, dotProduct, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul]
          fun_prop
      rw [hc] at hAll
      rw [rayleighQuotient_eq_div]
      exact (div_le_iff₀ (dotProduct_self_pos_of_ne_zero hy0)).mpr hAll
    · apply ciSup_le
      intro c
      split_ifs with hv
      · exact rayleighQuotient_le_lanczosRitzValue_of_mem_ne_zero hA b _
          (self_mem_krylovSpace_succ A b q) hb
      · exact rayleighQuotient_le_lanczosRitzValue_of_mem_ne_zero hA b _
          (krylovCoefficientVector_mem A b _) hv

/-- The largest Hermitian Krylov compression eigenvalue is measurable in the start. -/
theorem measurable_lanczosRitzValue {A : Matrix n n ℝ} (hA : A.IsHermitian) (q : ℕ) :
    Measurable (fun b : n → ℝ => lanczosRitzValue A b q) := by
  simp_rw [lanczosRitzValue_eq_iSup_rat hA]
  split_ifs
  · exact measurable_const
  · apply Measurable.iSup
    intro c
    have hv : Measurable (fun b : n → ℝ =>
        krylovCoefficientVector A b (fun j => (c j : ℝ))) := by
      simp only [krylovCoefficientVector]
      fun_prop
    have hr : Measurable (fun x : n → ℝ => rayleighQuotient A x) := by
      simp only [rayleighQuotient_eq_div, Matrix.mulVec, dotProduct]
      fun_prop
    exact Measurable.ite (show MeasurableSet {b |
      krylovCoefficientVector A b (fun j => (c j : ℝ)) = 0} from
      hv (measurableSet_singleton 0)) hr (hr.comp hv)

end NLAlib
