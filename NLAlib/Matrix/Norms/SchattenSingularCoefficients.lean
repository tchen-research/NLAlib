import NLAlib.Matrix.Norms.SchattenComparison
/-!
# Schatten norms of prescribed singular coefficients

Nonnegative decreasing coefficients in fixed unitary singular frames give
their exact power-sum norms and complex trace pairings. These are the explicit
attainer ingredients for Schatten duality over both real and complex scalars.
Source: Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12).
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Right multiplication by the conjugate transpose of a matrix with
orthonormal columns preserves the Frobenius pairing.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem frobInner_mul_conjTranspose_right_of_orthonormal {m n k : Type*}
    [Fintype m] [Fintype n] [Fintype k] [DecidableEq k]
    {V : Matrix n k 𝕜} (hV : HasOrthonormalCols V) (A B : Matrix m k 𝕜) :
    frobInner (A * Vᴴ) (B * Vᴴ) = frobInner A B := by
  rw [← frobInner_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,
    frobInner_mul_left_of_orthonormal hV, frobInner_conjTranspose]

/-- The full trace pairing of rectangular diagonals is their real
coefficient dot product, including empty diagonals.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem trace_conjTranspose_rectDiag_mul_rectDiag {m n : ℕ} (a b : ℕ → ℝ) :
    ((rectDiag a : Matrix (Fin m) (Fin n) 𝕜)ᴴ * rectDiag b).trace =
      ((∑ i ∈ Finset.range (min m n), a i * b i : ℝ) : 𝕜) := by
  have hcols : ((rectDiag a : Matrix (Fin m) (Fin n) 𝕜)ᴴ * rectDiag b).trace =
      ∑ j : Fin n, if j.val < m then ((a j * b j : ℝ) : 𝕜) else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < m
    · rw [Finset.sum_eq_single (⟨j.val, hj⟩ : Fin m)]
      · simp [rectDiag_apply_ofReal, hj, RCLike.star_def]
      · intro i _ hi
        have hij : i.val ≠ j.val := fun he => hi (Fin.ext he)
        simp [rectDiag_apply_ofReal, hij]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [hj]
      · intro i _
        have hij : i.val ≠ j.val := fun he => hj (he ▸ i.isLt)
        simp [rectDiag_apply_ofReal, hij]
  rw [hcols, Fin.sum_univ_eq_sum_range
    (fun j => if j < m then ((a j * b j : ℝ) : 𝕜) else 0) n, ← Finset.sum_filter]
  have hfilter : (Finset.range n).filter (fun j => j < m) = Finset.range (min m n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    tauto
  rw [hfilter]
  simp only [RCLike.ofReal_sum]

/-- The Frobenius pairing of rectangular diagonals is the thin real
coefficient dot product. Bhatia (1997), §IV.2. -/
theorem frobInner_rectDiag_rectDiag {m n : ℕ} (a b : ℕ → ℝ) :
    frobInner (rectDiag a : Matrix (Fin m) (Fin n) 𝕜) (rectDiag b) =
      ∑ i ∈ Finset.range (min m n), a i * b i := by
  rw [frobInner_eq_trace, trace_conjTranspose_rectDiag_mul_rectDiag, RCLike.ofReal_re]

open scoped Matrix.Norms.L2Operator in
/-- Prescribed decreasing nonnegative singular coefficients have their exact
Schatten power norm in fixed unitary frames over either scalar field.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem schattenNormReal_mul_rectDiag_mul_conjTranspose {m n : ℕ}
    {U : Matrix (Fin m) (Fin m) 𝕜} {V : Matrix (Fin n) (Fin n) 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (b : ℕ → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hb : Antitone b) (q : ℝ) :
    schattenNormReal (U * (rectDiag b : Matrix (Fin m) (Fin n) 𝕜) * Vᴴ) q =
      (∑ i ∈ Finset.range (min m n), b i ^ q) ^ (1 / q) := by
  unfold schattenNormReal
  simp only [Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [singularValues_eq_of_eq_mul_rectDiag_mul
    (A := U * (rectDiag b : Matrix (Fin m) (Fin n) 𝕜) * Vᴴ)
    hU hV hb0 hb rfl (Finset.mem_range.mp hi)]

/-- Pairing with prescribed coefficients in a matrix's own SVD frames gives
the exact full trace, as a real scalar in the coefficient field. In particular
the pairing has zero imaginary part over `ℂ`.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem IsSVD.trace_conjTranspose_mul_mul_rectDiag_mul_conjTranspose
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {p q : ℕ}
    {A : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜}
    {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (b : ℕ → ℝ) :
    (Aᴴ * (U * (rectDiag b : Matrix (Fin p) (Fin q) 𝕜) * Vᴴ)).trace =
      ((∑ i ∈ Finset.range (min p q), singularValues A i * b i : ℝ) : 𝕜) := by
  conv_lhs => rw [h.eq]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, h.conjTranspose_mul_left, Matrix.one_mul]
  rw [← Matrix.mul_assoc (rectDiag (singularValues A))ᴴ (rectDiag b),
    ← Matrix.mul_assoc V, Matrix.trace_mul_cycle, h.conjTranspose_mul_right,
    Matrix.one_mul, trace_conjTranspose_rectDiag_mul_rectDiag]

/-- The Frobenius pairing with prescribed coefficients in the same SVD
frames is the singular-value dot product. Bhatia (1997), §IV.2. -/
theorem IsSVD.frobInner_mul_rectDiag_mul_conjTranspose
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {p q : ℕ}
    {A : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜}
    {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (b : ℕ → ℝ) :
    frobInner A (U * (rectDiag b : Matrix (Fin p) (Fin q) 𝕜) * Vᴴ) =
      ∑ i ∈ Finset.range (min p q), singularValues A i * b i := by
  rw [frobInner_eq_trace, h.trace_conjTranspose_mul_mul_rectDiag_mul_conjTranspose,
    RCLike.ofReal_re]

end NLAlib
