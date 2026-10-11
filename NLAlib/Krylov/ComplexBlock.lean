import NLAlib.Matrix.PolynomialIntertwining
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Analysis.RCLike.Basic

/-!
# Actual complex block Krylov spaces

The column span of the native complex block powers contains every low-degree
real polynomial filter. Source: Musco--Musco (2015), polynomial competitor;
manuscript `sa:filter`, its block Krylov specialization.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib
variable {n s : Type*} [Fintype n] [DecidableEq n] [Fintype s]

/-- The actual complex block Krylov span of the first `q` block powers.
Source: Musco--Musco (2015), Alg. 2; manuscript `sa:filter`.
atlas: block-krylov-subspace (partial) -/
def complexBlockKrylovSpace (A : Matrix n n ℂ) (Ω : Matrix n s ℂ) (q : ℕ) :
    Submodule ℂ (n → ℂ) :=
  Submodule.span ℂ (Set.range fun ij : Fin q × s => ((A ^ (ij.1 : ℕ)) * Ω).col ij.2)

omit [DecidableEq n] [Fintype s] in
/-- A product's complex column is the native matrix applied to that column.
Source: matrix multiplication; helper for manuscript `sa:filter`. -/
theorem complex_col_mul_eq_mulVec_col {m : Type*}
    (M : Matrix m n ℂ) (Ω : Matrix n s ℂ) (j : s) : (M * Ω).col j = M *ᵥ Ω.col j := by
  ext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

omit [Fintype s] in
/-- Every native complex block power belongs to the block Krylov span.
Source: manuscript `sa:filter`, block Krylov definition. -/
theorem pow_mulVec_col_mem_complexBlockKrylovSpace (A : Matrix n n ℂ)
    (Ω : Matrix n s ℂ) {q i : ℕ} (hi : i < q) (j : s) :
    (A ^ i) *ᵥ Ω.col j ∈ complexBlockKrylovSpace A Ω q := by
  rw [← complex_col_mul_eq_mulVec_col]
  exact Submodule.subset_span ⟨(⟨i, hi⟩, j), rfl⟩

/-- Every real polynomial filter below the block Krylov order lies in the actual
complex block Krylov range. The zero polynomial includes order zero.
Source: manuscript `sa:filter`; Musco--Musco (2015), polynomial competitor. -/
theorem range_aeval_mul_le_complexBlockKrylovSpace
    (A : Matrix n n ℂ) (Ω : Matrix n s ℂ) {q : ℕ} {p : ℝ[X]} (hp : p.degree < q) :
    LinearMap.range (aeval A p * Ω).mulVecLin ≤ complexBlockKrylovSpace A Ω q := by
  by_cases hp0 : p = 0
  · subst hp0
    simp
  have hnat : p.natDegree < q := (natDegree_lt_iff_degree_lt hp0).mpr hp
  rw [Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  rw [complex_col_mul_eq_mulVec_col, aeval_eq_sum_range' hnat, Matrix.sum_mulVec]
  apply Submodule.sum_mem
  intro i hi
  rw [Matrix.smul_mulVec]
  have hs : p.coeff i • ((A ^ i) *ᵥ Ω.col j) =
      (p.coeff i : ℂ) • ((A ^ i) *ᵥ Ω.col j) := by
    ext a
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [hs]
  exact Submodule.smul_mem _ _
    (pow_mulVec_col_mem_complexBlockKrylovSpace A Ω (Finset.mem_range.mp hi) j)

end NLAlib
