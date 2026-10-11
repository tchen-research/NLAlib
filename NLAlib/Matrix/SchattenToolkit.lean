import NLAlib.Matrix.SchattenDuality
import NLAlib.Matrix.SchattenInvariant

/-!
# Complete schatten norms def contract

The clauses below are the actual universally quantified public statements,
assembled so that a full atlas tag certifies the entire family. Individual
clauses remain available in the imported topic modules.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
open scoped BigOperators ENNReal
namespace NLAlib
universe u_1 u_2 u_3

/-- All clauses of the schatten-norms-def result, with their original hypotheses,
constants, finite indices and endpoint conventions.
Components: `schattenNorm_one`, `schattenNorm_two`, `schattenNormExtended_top`, `schattenNormExtended_add_le`, `schattenNormExtended_smul`, `schattenNormExtended_eq_zero_iff`, `schattenNormExtended_orthogonal_mul`, `schattenNormExtended_mul_orthogonal`, `schattenNormExtended_transpose`, `abs_frobInner_le_schattenNormExtended_mul`, `schattenNormExtended_mul_le_mul`, `schattenNormExtended_le_of_le`, `schattenNormExtended_le_rank_rpow_mul`, `isGreatest_schattenNormExtended_frobInner`.
Source: bhatia97, §IV.2 (Schatten norms, Hölder); hj91, §3.3–3.4.
atlas: schatten-norms-def -/
theorem schatten_toolkit_properties :
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq n]
  (A : Matrix m n ℝ), NLAlib.schattenNorm A 1 = NLAlib.nuclearNorm A) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq n]
  (A : Matrix m n ℝ), NLAlib.schattenNorm A 2 = NLAlib.frobNorm A) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ), NLAlib.schattenNormExtended A ⊤ = NLAlib.specNorm A) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A B : Matrix m n ℝ) {p : ENNReal},
  1 ≤ p →
    NLAlib.schattenNormExtended (A + B) p ≤
      NLAlib.schattenNormExtended A p + NLAlib.schattenNormExtended B p) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) (c : ℝ) {p : ENNReal},
  1 ≤ p → NLAlib.schattenNormExtended (c • A) p = |c| * NLAlib.schattenNormExtended A p) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) {p : ENNReal},
  1 ≤ p → (NLAlib.schattenNormExtended A p = 0 ↔ A = 0)) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) {U : Matrix m m ℝ},
  NLAlib.HasOrthonormalCols U →
    ∀ (p : ENNReal), NLAlib.schattenNormExtended (U * A) p = NLAlib.schattenNormExtended A p) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) {V : Matrix n n ℝ},
  NLAlib.HasOrthonormalCols V →
    ∀ (p : ENNReal), NLAlib.schattenNormExtended (A * V) p = NLAlib.schattenNormExtended A p) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) (p : ENNReal),
  NLAlib.schattenNormExtended A.transpose p = NLAlib.schattenNormExtended A p) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A B : Matrix m n ℝ) {p s : ENNReal} [p.HolderConjugate s],
  |NLAlib.frobInner A B| ≤ NLAlib.schattenNormExtended A p * NLAlib.schattenNormExtended B s) ∧
    (∀ {m : Type u_1} {n : Type u_2} {q : Type u_3} [_inst : Fintype m] [_inst_1 : Fintype n]
  [_inst_2 : Fintype q] [_inst_3 : DecidableEq m] [_inst_4 : DecidableEq n] [_inst_5 : DecidableEq q]
  (A : Matrix m n ℝ) (B : Matrix n q ℝ) {p s r : ENNReal} [p.HolderTriple s r],
  1 ≤ p →
    1 ≤ s →
      1 ≤ r →
        NLAlib.schattenNormExtended (A * B) r ≤
          NLAlib.schattenNormExtended A p * NLAlib.schattenNormExtended B s) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) {p q : ENNReal},
  1 ≤ p → p ≤ q → NLAlib.schattenNormExtended A q ≤ NLAlib.schattenNormExtended A p) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) {p q : ENNReal},
  1 ≤ p →
    p ≤ q →
      NLAlib.schattenNormExtended A p ≤
        ↑A.rank ^ (p⁻¹.toReal - q⁻¹.toReal) * NLAlib.schattenNormExtended A q) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) {p q : ENNReal} [p.HolderConjugate q],
  IsGreatest
    {z : ℝ | ∃ (B : Matrix m n ℝ), NLAlib.schattenNormExtended B q ≤ 1 ∧ NLAlib.frobInner A B = z}
    (NLAlib.schattenNormExtended A p)) := by
  exact ⟨@NLAlib.schattenNorm_one,
    @NLAlib.schattenNorm_two,
    @NLAlib.schattenNormExtended_top,
    @NLAlib.schattenNormExtended_add_le,
    @NLAlib.schattenNormExtended_smul,
    @NLAlib.schattenNormExtended_eq_zero_iff,
    @NLAlib.schattenNormExtended_orthogonal_mul,
    @NLAlib.schattenNormExtended_mul_orthogonal,
    @NLAlib.schattenNormExtended_transpose,
    @NLAlib.abs_frobInner_le_schattenNormExtended_mul,
    @NLAlib.schattenNormExtended_mul_le_mul,
    @NLAlib.schattenNormExtended_le_of_le,
    @NLAlib.schattenNormExtended_le_rank_rpow_mul,
    @NLAlib.isGreatest_schattenNormExtended_frobInner⟩

end NLAlib
