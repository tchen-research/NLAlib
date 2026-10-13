import NLAlib.Matrix.Norms.Schatten
import NLAlib.Matrix.Norms.NuclearNorm
/-!
# Trace Hölder for Schatten norms

The absolute real trace inequality is derived from both signs of the checked
von Neumann inequality. Finite Hölder and the nuclear–spectral endpoints have
constant one and cover empty shapes without rank hypotheses.
Source: Bhatia (1997), §IV.2; Horn–Johnson (1991), §3.3–3.4.
Atlas: `schatten-norms-def`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

private theorem abs_frobInner_le_sum_singularValues_mul_fin {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    |frobInner A B| ≤ ∑ i ∈ Finset.range (min m n), singularValues A i * singularValues B i := by
  have hpos := frobInner_le_sum_singularValues_mul A B
  have hneg := frobInner_le_sum_singularValues_mul A (-B)
  rw [frobInner_neg_right, singularValues_neg] at hneg
  rw [abs_le]
  constructor <;> linarith

/-- Absolute-value von Neumann trace inequality
`|⟨A, B⟩_F| ≤ ∑_{i < min m n} σᵢ(A) σᵢ(B)` on arbitrary finite matrix index types. -/
theorem abs_frobInner_le_sum_singularValues_mul {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A B : Matrix m n ℝ) :
    |frobInner A B| ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A i * singularValues B i := by
  have h := abs_frobInner_le_sum_singularValues_mul_fin
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
    (B.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  simp only [frobInner_reindex, singularValues_reindex] at h
  exact h

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Schatten trace Hölder for all finite conjugate real exponents, with sharp
constant one and arbitrary finite matrix indices.
atlas: schatten-norms-def (partial) -/
theorem abs_frobInner_le_schattenNorm_mul (A B : Matrix m n ℝ) {p q : ℝ}
    (hpq : Real.HolderConjugate p q) : |frobInner A B| ≤ schattenNorm A p * schattenNorm B q := by
  apply (abs_frobInner_le_sum_singularValues_mul A B).trans
  exact Real.inner_le_Lp_mul_Lq_of_nonneg
    (Finset.range (min (Fintype.card m) (Fintype.card n)))
    (f := singularValues A) (g := singularValues B) hpq
    (fun i _ => singularValues_nonneg _ i) (fun i _ => singularValues_nonneg _ i)

open scoped Matrix.Norms.L2Operator in
/-- The `(1,∞)` Schatten trace Hölder endpoint, expressed in nuclear and
spectral norms. The constant is exactly one.
atlas: schatten-norms-def (partial) -/
theorem abs_frobInner_le_nuclearNorm_mul_specNorm (A B : Matrix m n ℝ) :
    |frobInner A B| ≤ nuclearNorm A * specNorm B := by
  calc
    |frobInner A B| ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i * singularValues B i :=
      abs_frobInner_le_sum_singularValues_mul A B
    _ ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i * specNorm B :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (singularValues_le_specNorm B i) (singularValues_nonneg _ i)
    _ = nuclearNorm A * specNorm B := by rw [← Finset.sum_mul]; rfl

open scoped Matrix.Norms.L2Operator in
/-- The `(∞,1)` Schatten trace Hölder endpoint, with exact constant one. -/
theorem abs_frobInner_le_specNorm_mul_nuclearNorm (A B : Matrix m n ℝ) :
    |frobInner A B| ≤ specNorm A * nuclearNorm B := by
  simpa only [frobInner_comm B A, mul_comm] using abs_frobInner_le_nuclearNorm_mul_specNorm B A

end NLAlib
