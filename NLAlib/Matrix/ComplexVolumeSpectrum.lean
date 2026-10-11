import NLAlib.Matrix.ComplexFrobenius
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Complex Gram spectrum and volume normalizers

The genuine complex Gram spectrum identifies the fixed-order principal-minor
normalizer with an elementary symmetric sum. Its positivity is exactly the
rank condition, including zero rank and empty index types. These deterministic
facts support manuscript `sa:volume-theorem`.
-/

noncomputable section
set_option autoImplicit false
open Polynomial
open scoped Matrix Matrix.Norms.Frobenius ComplexOrder
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The sorted, nonnegative eigenvalues of the actual complex column Gram
matrix. Source: the Hermitian spectral theorem; manuscript `sa:volume-theorem`. -/
def complexGramEigenvalues (A : Matrix m n ℂ) : Fin (Fintype.card n) → ℝ :=
  (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀

/-- The elementary symmetric Gram spectral sum on the native column labels.
Source: the determinant normalizer in manuscript `sa:volume-theorem`. -/
def complexGramElementary (A : Matrix m n ℂ) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.powersetCard k,
    ∏ i ∈ S, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i

/-- The sorted Gram spectral tail after removing `k` eigenvalues. Source:
Frobenius Eckart–Young; manuscript `sa:volume-theorem`. -/
def complexGramTail (A : Matrix m n ℂ) (k : ℕ) : ℝ :=
  ∑ i : Fin (Fintype.card n), if k ≤ (i : ℕ) then complexGramEigenvalues A i else 0

/-- Actual complex Gram eigenvalues are nonnegative. Source: positivity of
`AᴴA`; supports manuscript `sa:volume-theorem`. -/
theorem complexGramEigenvalues_nonneg (A : Matrix m n ℂ)
    (i : Fin (Fintype.card n)) : 0 ≤ complexGramEigenvalues A i := by
  have h := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A
    (Fintype.equivOfCardEq (Fintype.card_fin _) i)
  simpa [Matrix.IsHermitian.eigenvalues, complexGramEigenvalues] using h

/-- The actual complex Gram eigenvalues are in decreasing order. Source:
Mathlib's sorted Hermitian spectrum; supports `sa:volume-theorem`. -/
theorem complexGramEigenvalues_antitone (A : Matrix m n ℂ) :
    Antitone (complexGramEigenvalues A) :=
  (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀_antitone

/-- A nonnegative elementary symmetric sum is positive exactly when at least
`k` weights are nonzero. Source: the positive-support argument in the
volume-sampling normalizer, manuscript `sa:volume-theorem`. -/
theorem sum_powersetCard_prod_pos_iff_card_nonzero {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (k : ℕ) :
    0 < (∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, a i) ↔
      k ≤ Fintype.card {i // a i ≠ 0} := by
  classical
  let T := Finset.univ.filter fun i => a i ≠ 0
  have hcard : T.card = Fintype.card {i // a i ≠ 0} := by
    simp [T, Fintype.card_subtype]
  rw [← hcard]
  constructor
  · intro h
    obtain ⟨S, hS, hp⟩ :=
      (Finset.sum_pos_iff_of_nonneg fun S _ => Finset.prod_nonneg fun i _ => ha i).mp h
    have hST : S ⊆ T := by
      intro i hi
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hz => (ne_of_gt hp) (Finset.prod_eq_zero hi hz)
    exact (Finset.mem_powersetCard.mp hS).2.symm ▸ Finset.card_le_card hST
  · intro hk
    obtain ⟨S, hST, hSk⟩ := Finset.exists_subset_card_eq hk
    apply (Finset.sum_pos_iff_of_nonneg fun S _ =>
      Finset.prod_nonneg fun i _ => ha i).mpr
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hSk⟩, ?_⟩
    apply Finset.prod_pos
    intro i hi
    have hne : a i ≠ 0 := (Finset.mem_filter.mp (hST hi)).2
    exact lt_of_le_of_ne (ha i) (Ne.symm hne)

/-- The actual complex volume spectral normalizer is positive exactly at
feasible ranks, including rank zero. Source: manuscript `sa:volume-theorem`.
atlas: volume-sampling (partial) -/
theorem complexGramElementary_pos_iff (A : Matrix m n ℂ) (k : ℕ) :
    0 < complexGramElementary A k ↔ k ≤ A.rank := by
  rw [complexGramElementary, sum_powersetCard_prod_pos_iff_card_nonzero
    _ (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A)]
  rw [← (Matrix.isHermitian_conjTranspose_mul_self A).rank_eq_card_non_zero_eigs,
    Matrix.rank_conjTranspose_mul_self]

/-- Elementary Gram sums are nonnegative. Source: Gram positivity;
supports the probability normalizer of manuscript `sa:volume-theorem`. -/
theorem complexGramElementary_nonneg (A : Matrix m n ℂ) (k : ℕ) :
    0 ≤ complexGramElementary A k := by
  exact Finset.sum_nonneg fun S _ => Finset.prod_nonneg fun i _ =>
    Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i

/-- Infeasible ranks have zero complex volume normalizer. Source: the rank
condition in manuscript `sa:volume-theorem`. -/
theorem complexGramElementary_eq_zero_of_rank_lt (A : Matrix m n ℂ) {k : ℕ}
    (hk : A.rank < k) : complexGramElementary A k = 0 := by
  exact le_antisymm (not_lt.mp (by
    simpa [complexGramElementary_pos_iff] using not_le.mpr hk))
    (complexGramElementary_nonneg A k)

/-- The order-zero spectral normalizer equals one for every complex matrix.
Source: the empty determinant convention in manuscript `sa:volume-theorem`. -/
@[simp] theorem complexGramElementary_zero (A : Matrix m n ℂ) :
    complexGramElementary A 0 = 1 := by simp [complexGramElementary]

/-- Similarity preserves the determinant polynomial `det(I+tG)` over any
commutative ring. Source: the determinant coefficient proof of
manuscript `sa:volume-theorem`; no reality assumption is needed. -/
theorem det_one_add_X_smul_eq_of_diagonalization {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] {G U V : Matrix ι ι R} {d : ι → R}
    (hVU : V * U = 1) (hG : G = U * Matrix.diagonal d * V) :
    Matrix.det (1 + (X : R[X]) • G.map C) =
      Matrix.det (1 + (X : R[X]) • (Matrix.diagonal d).map C) := by
  let Up : Matrix ι ι R[X] := U.map C
  let Vp : Matrix ι ι R[X] := V.map C
  let Dp : Matrix ι ι R[X] := (Matrix.diagonal d).map C
  have hp : Vp * Up = 1 := by
    have h := congrArg (fun M : Matrix ι ι R => M.map C) hVU
    simpa [Up, Vp, Matrix.map_mul, Matrix.map_one] using h
  have hp' : Up * Vp = 1 := mul_eq_one_comm.1 hp
  have hg : G.map C = Up * Dp * Vp := by
    rw [hG, Matrix.map_mul, Matrix.map_mul]
  have he : 1 + (X : R[X]) • G.map C = Up * (1 + (X : R[X]) • Dp) * Vp := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hp']
    simp only [Matrix.mul_smul, Matrix.smul_mul, hg]
  have hd : Up.det * Vp.det = 1 := by rw [← Matrix.det_mul, hp', Matrix.det_one]
  rw [he, Matrix.det_mul, Matrix.det_mul]
  dsimp only [Dp]
  calc
    Up.det * (1 + (X : R[X]) • (Matrix.diagonal d).map C).det * Vp.det =
        (Up.det * Vp.det) * (1 + (X : R[X]) • (Matrix.diagonal d).map C).det := by ring
    _ = _ := by rw [hd, one_mul]

/-- The sum of fixed-order complex Hermitian principal determinants equals
the elementary sum of the actual eigenvalues. Source: the Hermitian spectral
theorem and determinant coefficient proof of manuscript `sa:volume-theorem`. -/
theorem sum_det_principal_minors_eq_sum_prod_of_isHermitian {G : Matrix n n ℂ}
    (hG : G.IsHermitian) (k : ℕ) :
    (∑ S ∈ Finset.univ.powersetCard k, (G.submatrix
      (Subtype.val : S → n) (Subtype.val : S → n)).det) =
      ∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, (hG.eigenvalues i : ℂ) := by
  have hd : G = (hG.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => (hG.eigenvalues i : ℂ)) *
      star (hG.eigenvectorUnitary : Matrix n n ℂ) := by
    simpa [Unitary.conjStarAlgAut_apply, Function.comp_def] using hG.spectral_theorem
  rw [← Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    det_one_add_X_smul_eq_of_diagonalization
      (Unitary.coe_star_mul_self hG.eigenvectorUnitary) hd,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  apply Finset.sum_congr rfl
  intro S _
  have hD : (Matrix.diagonal (fun i => (hG.eigenvalues i : ℂ))).submatrix
      (Subtype.val : S → n) (Subtype.val : S → n) =
      Matrix.diagonal (fun i : S => (hG.eigenvalues i : ℂ)) := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.diagonal_apply]
  rw [hD, Matrix.det_diagonal]
  exact Finset.prod_coe_sort S (fun i => (hG.eigenvalues i : ℂ))

/-- The real complex Gram principal-minor normalizer equals its actual
elementary spectral sum. Source: manuscript `sa:volume-theorem`.
atlas: volume-sampling (partial) -/
theorem sum_re_det_complex_gram_principal_minors_eq (A : Matrix m n ℂ) (k : ℕ) :
    (∑ S ∈ Finset.univ.powersetCard k, ((Aᴴ * A).submatrix
      (Subtype.val : S → n) (Subtype.val : S → n)).det.re) =
      complexGramElementary A k := by
  have h := congrArg Complex.re
    (sum_det_principal_minors_eq_sum_prod_of_isHermitian
      (Matrix.isHermitian_conjTranspose_mul_self A) k)
  simpa [complexGramElementary, ← Complex.ofReal_prod] using h

/-- Elementary spectral sums commute with relabeling by an equivalence.
Source: finite spectral relabeling; supports `sa:volume-theorem`. -/
theorem sum_powersetCard_prod_eq_of_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (a : κ → ℝ) (k : ℕ) :
    (∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, a i) =
      ∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, a (e i) := by
  rw [← Finset.map_univ_equiv e, Finset.powersetCard_map, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro S _
  change (∏ i ∈ S.map e.toEmbedding, a i) = ∏ i ∈ S, a (e i)
  exact Finset.prod_map S e.toEmbedding a

/-- The native-index Gram normalizer equals the elementary sum of the sorted
Gram eigenvalues. Source: the spectral determinant proof in
manuscript `sa:volume-theorem`. -/
theorem complexGramElementary_eq_sum_prod_sorted (A : Matrix m n ℂ) (k : ℕ) :
    complexGramElementary A k =
      ∑ S ∈ (Finset.univ : Finset (Fin (Fintype.card n))).powersetCard k,
        ∏ i ∈ S, complexGramEigenvalues A i := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  rw [complexGramElementary, sum_powersetCard_prod_eq_of_equiv e]
  simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply,
    complexGramEigenvalues]

end NLAlib
