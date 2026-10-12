import NLAlib.Matrix.Norms.Schatten
import NLAlib.Matrix.Norms.NuclearFiniteIndex
import NLAlib.Matrix.Spectral.SingularValueInvariance
/-!
# Trace Hölder for Schatten norms

The absolute real trace inequality is derived from both signs of the checked
von Neumann inequality. Finite Hölder and the nuclear–spectral endpoints have
constant one and cover empty shapes without rank hypotheses.
Source: Bhatia (1997), §IV.2; Horn–Johnson (1991), §3.3–3.4.
Atlas: `schatten-norms-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

/-- Every native singular value is at most the spectral norm, on arbitrary
finite matrix indices and including padded zeros. -/
theorem toEuclideanLin_singularValues_le_specNorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) (i : ℕ) :
    A.toEuclideanLin.singularValues i ≤ specNorm A := by
  have h := kyFanNorm_one_eq_specNorm A
  simp only [kyFanNorm, Finset.sum_range_one] at h
  exact (LinearMap.singularValues_antitone _ (Nat.zero_le i)).trans_eq h

/-- Absolute-value real von Neumann trace inequality, over finite matrix shapes. -/
theorem abs_frobInner_le_sum_singularValues_mul_fin {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    |frobInner A B| ≤ ∑ i ∈ Finset.range (min m n), singularValues A i * singularValues B i := by
  have hpos := frobInner_le_sum_singularValues_mul A B
  have hneg := frobInner_le_sum_singularValues_mul A (-B)
  rw [frobInner_neg_right, singularValues_neg] at hneg
  rw [abs_le]
  constructor <;> linarith

/-- Absolute-value von Neumann trace inequality in native singular values on
arbitrary finite matrix index types. -/
theorem abs_frobInner_le_sum_toEuclideanLin_singularValues_mul {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A B : Matrix m n ℝ) :
    |frobInner A B| ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      A.toEuclideanLin.singularValues i * B.toEuclideanLin.singularValues i := by
  have h := abs_frobInner_le_sum_singularValues_mul_fin
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
    (B.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  simpa only [frobInner_reindex, singularValues_reindex_eq_toEuclideanLin_singularValues] using h

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Schatten trace Hölder for all finite conjugate real exponents, with sharp
constant one and arbitrary finite matrix indices.
atlas: schatten-norms-def (partial) -/
theorem abs_frobInner_le_schattenNorm_mul (A B : Matrix m n ℝ) {p q : ℝ}
    (hpq : Real.HolderConjugate p q) : |frobInner A B| ≤ schattenNorm A p * schattenNorm B q := by
  apply (abs_frobInner_le_sum_toEuclideanLin_singularValues_mul A B).trans
  exact Real.inner_le_Lp_mul_Lq_of_nonneg
    (Finset.range (min (Fintype.card m) (Fintype.card n)))
    (f := A.toEuclideanLin.singularValues) (g := B.toEuclideanLin.singularValues) hpq
    (fun i _ => LinearMap.singularValues_nonneg _ i) (fun i _ => LinearMap.singularValues_nonneg _ i)

/-- The `(1,∞)` Schatten trace Hölder endpoint, expressed in nuclear and
spectral norms. The constant is exactly one.
atlas: schatten-norms-def (partial) -/
theorem abs_frobInner_le_nuclearNorm_mul_specNorm (A B : Matrix m n ℝ) :
    |frobInner A B| ≤ nuclearNorm A * specNorm B := by
  calc
    |frobInner A B| ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        A.toEuclideanLin.singularValues i * B.toEuclideanLin.singularValues i :=
      abs_frobInner_le_sum_toEuclideanLin_singularValues_mul A B
    _ ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        A.toEuclideanLin.singularValues i * specNorm B :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (toEuclideanLin_singularValues_le_specNorm B i) (LinearMap.singularValues_nonneg _ i)
    _ = nuclearNorm A * specNorm B := by rw [← Finset.sum_mul]; rfl

/-- The `(∞,1)` Schatten trace Hölder endpoint, with exact constant one. -/
theorem abs_frobInner_le_specNorm_mul_nuclearNorm (A B : Matrix m n ℝ) :
    |frobInner A B| ≤ specNorm A * nuclearNorm B := by
  simpa only [frobInner_comm B A, mul_comm] using abs_frobInner_le_nuclearNorm_mul_specNorm B A

end NLAlib
