import NLAlib.Matrix.Structured.KroneckerSingularValues
import NLAlib.Matrix.Structured.KroneckerIdentities
/-!
# Complete kronecker spectral contract

The clauses below are the actual universally quantified public statements,
assembled so that a full atlas tag certifies the entire family. Individual
clauses remain available in the imported topic modules.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
open scoped BigOperators ENNReal
namespace NLAlib
universe u_1 u_2 u_3 u_4

/-- All clauses of the kronecker-spectral result, with their original hypotheses,
constants, finite indices and endpoint conventions.
Components: `IsSVD.kronecker_factorization`, `multiset_toEuclideanLin_singularValues_kronecker`, `multiset_eigenvalues_kronecker`, `multiset_eigenvalues_kronecker_sum`, `specNorm_kronecker`, `frobNorm_kronecker`, `rank_kronecker`, `moorePenroseInverse_kronecker`.
Source: hj91, Thm 4.2.12 (eigenvalues), Thm 4.2.15 (SVD); vl00, §2.
atlas: kronecker-spectral -/
theorem kronecker_toolkit_properties :
    (∀ {m n p q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin p) (Fin q) ℝ}
  {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ} {P : Matrix (Fin p) (Fin p) ℝ}
  {Q : Matrix (Fin q) (Fin q) ℝ},
  NLAlib.IsSVD A U V →
    NLAlib.IsSVD B P Q →
      Matrix.kroneckerMap (fun (x1 x2 : ℝ) => x1 * x2) A B =
        Matrix.kroneckerMap (fun (x1 x2 : ℝ) => x1 * x2) U P *
            Matrix.kroneckerMap (fun (x1 x2 : ℝ) => x1 * x2)
              (NLAlib.rectDiag (NLAlib.singularValues A) : Matrix (Fin m) (Fin n) ℝ)
              (NLAlib.rectDiag (NLAlib.singularValues B) : Matrix (Fin p) (Fin q) ℝ) *
          (Matrix.kroneckerMap (fun (x1 x2 : ℝ) => x1 * x2) V Q).transpose) ∧
    (∀ {m : Type u_1} {n : Type u_2} {p : Type u_3} {q : Type u_4} [_inst : Fintype m]
  [_inst_1 : Fintype n] [_inst_2 : Fintype p] [_inst_3 : Fintype q] [_inst_4 : DecidableEq n]
  [_inst_5 : DecidableEq q] (A : Matrix m n ℝ) (B : Matrix p q ℝ),
  Multiset.map
      (fun (i : Fin (Fintype.card (n × q))) =>
        (Matrix.toEuclideanLin
              (Matrix.kroneckerMap (fun (x1 x2 : ℝ) => x1 * x2) A B)).singularValues
          ↑i)
      Finset.univ.val =
    Multiset.map (fun (xy : ℝ × ℝ) => xy.1 * xy.2)
      (Multiset.map (fun (i : Fin (Fintype.card n)) => (Matrix.toEuclideanLin A).singularValues ↑i)
          Finset.univ.val ×ˢ
        Multiset.map (fun (i : Fin (Fintype.card q)) => (Matrix.toEuclideanLin B).singularValues ↑i)
          Finset.univ.val)) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] {A : Matrix m m ℝ} {B : Matrix n n ℝ} (hA : A.IsHermitian)
  (hB : B.IsHermitian),
  Multiset.map (NLAlib.isHermitian_kronecker hA hB).eigenvalues Finset.univ.val =
    Multiset.map (fun (ij : m × n) => hA.eigenvalues ij.1 * hB.eigenvalues ij.2) Finset.univ.val) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] {A : Matrix m m ℝ} {B : Matrix n n ℝ} (hA : A.IsHermitian)
  (hB : B.IsHermitian),
  Multiset.map
      (Matrix.IsHermitian.add (NLAlib.isHermitian_kronecker hA Matrix.isHermitian_one)
          (NLAlib.isHermitian_kronecker Matrix.isHermitian_one hB)).eigenvalues
      Finset.univ.val =
    Multiset.map (fun (ij : m × n) => hA.eigenvalues ij.1 + hB.eigenvalues ij.2) Finset.univ.val) ∧
    (∀ {m : Type u_1} {n : Type u_2} {p : Type u_3} {q : Type u_4} [_inst : Fintype m]
  [_inst_1 : Fintype n] [_inst_2 : Fintype p] [_inst_3 : Fintype q] [_inst_4 : DecidableEq m]
  [_inst_5 : DecidableEq n] [_inst_6 : DecidableEq p] [_inst_7 : DecidableEq q] (A : Matrix m n ℝ)
  (B : Matrix p q ℝ),
  NLAlib.specNorm (Matrix.kroneckerMap (fun (x1 x2 : ℝ) => x1 * x2) A B) =
    NLAlib.specNorm A * NLAlib.specNorm B) ∧
    (∀ {m : Type u_1} {n : Type u_2} {p : Type u_3} {q : Type u_4} [_inst : Fintype m]
  [_inst_1 : Fintype n] [_inst_2 : Fintype p] [_inst_3 : Fintype q] (A : Matrix m n ℝ)
  (B : Matrix p q ℝ),
  NLAlib.frobNorm (Matrix.kroneckerMap (fun (x1 x2 : ℝ) => x1 * x2) A B) =
    NLAlib.frobNorm A * NLAlib.frobNorm B) ∧
    (∀ {m : Type u_1} {n : Type u_2} {p : Type u_3} {q : Type u_4} [Fintype m] [_inst : Fintype n]
  [Fintype p] [_inst_2 : Fintype q] (A : Matrix m n ℝ) (B : Matrix p q ℝ),
  (Matrix.kroneckerMap (fun (x1 x2 : ℝ) => x1 * x2) A B).rank = A.rank * B.rank) ∧
    (∀ {m : Type u_1} {n : Type u_2} {p : Type u_3} {q : Type u_4} [_inst : Fintype m]
  [_inst_1 : Fintype n] [_inst_2 : Fintype p] [_inst_3 : Fintype q] (A : Matrix m n ℝ)
  (B : Matrix p q ℝ),
  NLAlib.moorePenroseInverse (Matrix.kroneckerMap (fun (x1 x2 : ℝ) => x1 * x2) A B) =
    Matrix.kroneckerMap (fun (x1 x2 : ℝ) => x1 * x2) (NLAlib.moorePenroseInverse A)
      (NLAlib.moorePenroseInverse B)) := by
  exact ⟨@NLAlib.IsSVD.kronecker_factorization,
    @NLAlib.multiset_toEuclideanLin_singularValues_kronecker,
    @NLAlib.multiset_eigenvalues_kronecker,
    @NLAlib.multiset_eigenvalues_kronecker_sum,
    @NLAlib.specNorm_kronecker,
    @NLAlib.frobNorm_kronecker,
    @NLAlib.rank_kronecker,
    @NLAlib.moorePenroseInverse_kronecker⟩

end NLAlib
