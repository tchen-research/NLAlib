import NLAlib.Matrix.NuclearPSD
import NLAlib.Matrix.NuclearFiniteIndex
import NLAlib.Matrix.KyFanFiniteIndex

/-!
# Complete ky fan norms def contract

The clauses below are the actual universally quantified public statements,
assembled so that a full atlas tag certifies the entire family. Individual
clauses remain available in the imported topic modules.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
open scoped BigOperators ENNReal
namespace NLAlib
universe u_1 u_2

/-- All clauses of the ky-fan-norms-def result, with their original hypotheses,
constants, finite indices and endpoint conventions.
Components: `kyFanNorm_nonneg`, `kyFanNorm_add_le`, `kyFanNorm_smul`, `kyFanNorm_eq_zero_iff`, `kyFanNorm_orthogonal_mul`, `kyFanNorm_mul_orthogonal`, `kyFanNorm_transpose`, `kyFanNorm_one_eq_specNorm`, `nuclearNorm_add_le`, `nuclearNorm_smul`, `nuclearNorm_eq_zero_iff`, `nuclearNorm_orthogonal_mul`, `nuclearNorm_mul_orthogonal`, `nuclearNorm_transpose`, `isGreatest_nuclearNorm_frobInner`, `nuclearNorm_eq_trace_of_posSemidef`, `specNorm_le_nuclearNorm`, `nuclearNorm_le_rank_mul_specNorm`, `frobNorm_le_nuclearNorm`, `nuclearNorm_le_sqrt_rank_mul_frobNorm`.
Source: hj91, Thm 3.4.1, Cor 3.4.4; bhatia97, §IV.2.
atlas: ky-fan-norms-def -/
theorem ky_fan_norm_toolkit_properties :
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq n]
  (A : Matrix m n ℝ) (k : ℕ), 0 ≤ NLAlib.kyFanNorm A k) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq n]
  (A B : Matrix m n ℝ) (k : ℕ),
  NLAlib.kyFanNorm (A + B) k ≤ NLAlib.kyFanNorm A k + NLAlib.kyFanNorm B k) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq n]
  (A : Matrix m n ℝ) (c : ℝ) (k : ℕ), NLAlib.kyFanNorm (c • A) k = |c| * NLAlib.kyFanNorm A k) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) {k : ℕ}, 1 ≤ k → (NLAlib.kyFanNorm A k = 0 ↔ A = 0)) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) {U : Matrix m m ℝ},
  NLAlib.HasOrthonormalCols U → ∀ (k : ℕ), NLAlib.kyFanNorm (U * A) k = NLAlib.kyFanNorm A k) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq n]
  (A : Matrix m n ℝ) {V : Matrix n n ℝ},
  NLAlib.HasOrthonormalCols V → ∀ (k : ℕ), NLAlib.kyFanNorm (A * V) k = NLAlib.kyFanNorm A k) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) (k : ℕ),
  NLAlib.kyFanNorm A.transpose k = NLAlib.kyFanNorm A k) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ), NLAlib.kyFanNorm A 1 = NLAlib.specNorm A) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [DecidableEq m]
  [_inst_3 : DecidableEq n] (A B : Matrix m n ℝ),
  NLAlib.nuclearNorm (A + B) ≤ NLAlib.nuclearNorm A + NLAlib.nuclearNorm B) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) (c : ℝ),
  NLAlib.nuclearNorm (c • A) = |c| * NLAlib.nuclearNorm A) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ), NLAlib.nuclearNorm A = 0 ↔ A = 0) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) {U : Matrix m m ℝ},
  NLAlib.HasOrthonormalCols U → NLAlib.nuclearNorm (U * A) = NLAlib.nuclearNorm A) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ) {V : Matrix n n ℝ},
  NLAlib.HasOrthonormalCols V → NLAlib.nuclearNorm (A * V) = NLAlib.nuclearNorm A) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ), NLAlib.nuclearNorm A.transpose = NLAlib.nuclearNorm A) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ),
  IsGreatest {z : ℝ | ∃ (B : Matrix m n ℝ), NLAlib.specNorm B ≤ 1 ∧ NLAlib.frobInner A B = z}
    (NLAlib.nuclearNorm A)) ∧
    (∀ {n : Type u_1} [_inst : Fintype n] [_inst_1 : DecidableEq n] {A : Matrix n n ℝ},
  A.PosSemidef → NLAlib.nuclearNorm A = A.trace) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ), NLAlib.specNorm A ≤ NLAlib.nuclearNorm A) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A : Matrix m n ℝ), NLAlib.nuclearNorm A ≤ ↑A.rank * NLAlib.specNorm A) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq n]
  (A : Matrix m n ℝ), NLAlib.frobNorm A ≤ NLAlib.nuclearNorm A) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq n]
  (A : Matrix m n ℝ), NLAlib.nuclearNorm A ≤ √↑A.rank * NLAlib.frobNorm A) := by
  exact ⟨@NLAlib.kyFanNorm_nonneg,
    @NLAlib.kyFanNorm_add_le,
    @NLAlib.kyFanNorm_smul,
    @NLAlib.kyFanNorm_eq_zero_iff,
    @NLAlib.kyFanNorm_orthogonal_mul,
    @NLAlib.kyFanNorm_mul_orthogonal,
    @NLAlib.kyFanNorm_transpose,
    @NLAlib.kyFanNorm_one_eq_specNorm,
    (by intros; apply NLAlib.nuclearNorm_add_le),
    (by intros; apply NLAlib.nuclearNorm_smul),
    @NLAlib.nuclearNorm_eq_zero_iff,
    @NLAlib.nuclearNorm_orthogonal_mul,
    (by intros; apply NLAlib.nuclearNorm_mul_orthogonal; assumption),
    @NLAlib.nuclearNorm_transpose,
    @NLAlib.isGreatest_nuclearNorm_frobInner,
    @NLAlib.nuclearNorm_eq_trace_of_posSemidef,
    @NLAlib.specNorm_le_nuclearNorm,
    @NLAlib.nuclearNorm_le_rank_mul_specNorm,
    @NLAlib.frobNorm_le_nuclearNorm,
    @NLAlib.nuclearNorm_le_sqrt_rank_mul_frobNorm⟩

end NLAlib
