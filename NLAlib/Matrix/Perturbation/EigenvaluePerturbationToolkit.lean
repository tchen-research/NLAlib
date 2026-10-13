import NLAlib.Matrix.Perturbation.EigenvalueTrace
/-!
# Complete eigenvalue perturbation symmetric contract

The clauses below are the actual universally quantified public statements,
assembled so that a full atlas tag certifies the entire family. Individual
clauses remain available in the imported topic modules.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
open scoped ENNReal
namespace NLAlib
universe u_1

/-- All clauses of the eigenvalue-perturbation-symmetric result, with their original hypotheses,
constants, finite indices and endpoint conventions.
Components: `eigenvalues₀_add_le_add_eigenvalues₀_zero`, `add_eigenvalues₀_last_le_eigenvalues₀_add`, `abs_eigenvalues₀_add_sub_le_specNorm`, `trace_mul_le_sum_eigenvalues₀_mul`, `sum_sq_eigenvalues₀_add_sub_le_frobSq`.
Source: hj13, Thm 4.3.1, Cor 4.3.15 (Weyl); Cor 6.3.8 (Hoffman–Wielandt); bhatia97, Cor III.2.6, Thm VI.4.1.
atlas: eigenvalue-perturbation-symmetric -/
theorem eigenvalue_perturbation_toolkit_properties :
    (∀ {n : Type u_1} [_inst : Fintype n] [_inst_1 : DecidableEq n] {A E : Matrix n n ℝ}
  (hA : A.IsHermitian) (hE : E.IsHermitian) (i : Fin (Fintype.card n)),
  (Matrix.IsHermitian.add hA hE).eigenvalues₀ i ≤
    hA.eigenvalues₀ i +
      hE.eigenvalues₀
        ⟨0, by have := i.isLt; omega⟩) ∧
    (∀ {n : Type u_1} [_inst : Fintype n] [_inst_1 : DecidableEq n] {A E : Matrix n n ℝ}
  (hA : A.IsHermitian) (hE : E.IsHermitian) (i : Fin (Fintype.card n)),
  hA.eigenvalues₀ i +
      hE.eigenvalues₀
        ⟨Fintype.card n - 1, by have := i.isLt; omega⟩ ≤
    (Matrix.IsHermitian.add hA hE).eigenvalues₀ i) ∧
    (∀ {n : Type u_1} [_inst : Fintype n] [_inst_1 : DecidableEq n] {A E : Matrix n n ℝ}
  (hA : A.IsHermitian) (hE : E.IsHermitian) (i : Fin (Fintype.card n)),
  |(Matrix.IsHermitian.add hA hE).eigenvalues₀ i - hA.eigenvalues₀ i| ≤ NLAlib.specNorm E) ∧
    (∀ {n : Type u_1} [_inst : Fintype n] [_inst_1 : DecidableEq n] {A B : Matrix n n ℝ}
  (hA : A.IsHermitian) (hB : B.IsHermitian),
  (A * B).trace ≤ ∑ i : Fin (Fintype.card n), hA.eigenvalues₀ i * hB.eigenvalues₀ i) ∧
    (∀ {n : Type u_1} [_inst : Fintype n] [_inst_1 : DecidableEq n] {A E : Matrix n n ℝ}
  (hA : A.IsHermitian) (hE : E.IsHermitian),
  ∑ i : Fin (Fintype.card n),
      ((Matrix.IsHermitian.add hA hE).eigenvalues₀ i - hA.eigenvalues₀ i) ^ 2 ≤
    NLAlib.frobSq E) := by
  exact ⟨@NLAlib.eigenvalues₀_add_le_add_eigenvalues₀_zero,
    @NLAlib.add_eigenvalues₀_last_le_eigenvalues₀_add,
    @NLAlib.abs_eigenvalues₀_add_sub_le_specNorm,
    @NLAlib.trace_mul_le_sum_eigenvalues₀_mul,
    @NLAlib.sum_sq_eigenvalues₀_add_sub_le_frobSq⟩

end NLAlib
