import NLAlib.Matrix.Factorizations.NearestPolar
/-!
# The dimensionally correct cosine–sine canonical matrix

One cosine/sine pair acts on each first-block coordinate. A column isometry
embeds the second copy in the larger block, and its orthogonal complement is
fixed. The construction divides by neither cosine nor sine.
Horn–Johnson 2013, Theorem 2.7.1; atlas `cs-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- The CS canonical matrix, with cosine diagonal `c`, sine diagonal
`sqrt(1-c²)`, one block of each size on both sides, and identity on the
coordinate-frame complement. Choosing the first-column inclusion gives
the usual three-block `p,p,q-p` display. Horn–Johnson 2013, Theorem 2.7.1.
atlas: cs-decomposition (partial) -/
def csCanonicalMatrix {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (c : p → ℝ) (E : Matrix q p ℝ) : Matrix (p ⊕ q) (p ⊕ q) ℝ :=
  let C := Matrix.diagonal c
  let S := Matrix.diagonal (fun i => Real.sqrt (1 - c i ^ 2))
  Matrix.fromBlocks C (S * Eᵀ) (-E * S) (E * C * Eᵀ + 1 - E * Eᵀ)

/-- Nonnegative cosines no larger than one and a column-isometric coordinate
inclusion produce an orthogonal CS canonical matrix. Both angle endpoints
and empty dimensions are included. Horn–Johnson 2013, Theorem 2.7.1.
atlas: cs-decomposition (partial) -/
theorem hasOrthonormalCols_csCanonicalMatrix {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (c : p → ℝ) (E : Matrix q p ℝ) (hE : HasOrthonormalCols E)
    (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1) : HasOrthonormalCols (csCanonicalMatrix c E) := by
  let C := Matrix.diagonal c
  let S := Matrix.diagonal (fun i => Real.sqrt (1 - c i ^ 2))
  let R := E * C * Eᵀ + 1 - E * Eᵀ
  have hCt : Cᵀ = C := Matrix.diagonal_transpose _
  have hSt : Sᵀ = S := Matrix.diagonal_transpose _
  have hSum : C * C + S * S = 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      have hNonneg : 0 ≤ 1 - c i ^ 2 := by nlinarith [(hc i).1, (hc i).2]
      rw [Real.mul_self_sqrt hNonneg]
      ring
    · simp [Matrix.add_apply, hij]
  have hCS : C * S = S * C := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hRt : Rᵀ = R := by
    dsimp [R]
    simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_one, hCt, Matrix.mul_assoc]
  have hRE : R * E = E * C := by
    dsimp [R]
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [hE.transpose_mul_self, Matrix.mul_one, Matrix.mul_one]
    abel
  have hER : Eᵀ * R = C * Eᵀ := by
    have h := congrArg Matrix.transpose hRE
    simpa only [Matrix.transpose_mul, hRt, hCt] using h
  have hRR : R * R = E * C * C * Eᵀ + 1 - E * Eᵀ := by
    calc
      R * R = R * E * C * Eᵀ + R - R * E * Eᵀ := by
        nth_rw 2 [show R = E * C * Eᵀ + 1 - E * Eᵀ from rfl]
        simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
      _ = E * C * C * Eᵀ + 1 - E * Eᵀ := by
        rw [hRE]
        dsimp [R]
        simp only [Matrix.mul_assoc]
        abel
  have h11 : Cᵀ * C + (-E * S)ᵀ * (-E * S) = 1 := by
    simp only [Matrix.transpose_mul, Matrix.transpose_neg, hCt, hSt,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Eᵀ E S, hE.transpose_mul_self, Matrix.one_mul]
    exact hSum
  have h12 : Cᵀ * (S * Eᵀ) + (-E * S)ᵀ * R = 0 := by
    simp only [Matrix.transpose_mul, Matrix.transpose_neg, hCt, hSt,
      Matrix.neg_mul, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc S Eᵀ R, hER, ← Matrix.mul_assoc S C Eᵀ, ← hCS]
    abel
  have h21 : (S * Eᵀ)ᵀ * C + Rᵀ * (-E * S) = 0 := by
    have h := congrArg Matrix.transpose h12
    simpa only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero] using h
  have h22 : (S * Eᵀ)ᵀ * (S * Eᵀ) + Rᵀ * R = 1 := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hSt, hRt]
    rw [hRR]
    have hPair : (E * S) * (S * Eᵀ) + E * C * C * Eᵀ = E * Eᵀ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_add, ← Matrix.mul_assoc S S Eᵀ, ← Matrix.mul_assoc C C Eᵀ,
        ← Matrix.add_mul]
      rw [add_comm (S * S) (C * C), hSum, Matrix.one_mul]
    calc
      _ = ((E * S) * (S * Eᵀ) + E * C * C * Eᵀ) + 1 - E * Eᵀ := by abel
      _ = 1 := by rw [hPair]; abel
  change (Matrix.fromBlocks C (S * Eᵀ) (-E * S) R)ᵀ *
    Matrix.fromBlocks C (S * Eᵀ) (-E * S) R = 1
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, h11, h12, h21, h22,
    Matrix.fromBlocks_one]

end NLAlib
