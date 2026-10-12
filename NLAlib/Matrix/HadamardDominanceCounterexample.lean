import NLAlib.Matrix.HadamardOrder

/-!
# The Hermitian hypothesis in Hadamard quadratic dominance

An explicit real nonsymmetric comparand satisfies quadratic dominance by
identity, but its Hadamard square violates the corresponding product bound.
This records the necessary source-scope repair for
`schur-product-inequalities`, Horn--Johnson (2013), Theorem 7.8.16.
-/

noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib

/-- Dropping symmetry from the Hadamard quadratic-dominance statement is
false: the nilpotent matrix with upper-right entry two is dominated by
identity, but its Hadamard square has upper-right entry four and violates
dominance at the all-ones vector. Explicit repair of the overbroad wording
of Horn--Johnson (2013), Theorem 7.8.16; `schur-product-inequalities`. -/
theorem exists_nonsymmetric_quadratic_dominance_not_hadamard_preserved :
    ∃ B : Matrix (Fin 2) (Fin 2) ℝ, ¬B.IsHermitian ∧
      (∀ x : Fin 2 → ℝ, |quadForm B x| ≤ quadForm (1 : Matrix (Fin 2) (Fin 2) ℝ) x) ∧
      ∃ x : Fin 2 → ℝ,
        quadForm ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊙ 1) x < |quadForm (B ⊙ B) x| := by
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 0, 0]
  refine ⟨B, ?_, ?_, ?_⟩
  · intro h
    have hh := h.apply (0 : Fin 2) 1
    norm_num [B] at hh
  · intro x
    simp [quadForm, B, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
    nlinarith [sq_nonneg (|x 0| - |x 1|), sq_abs (x 0), sq_abs (x 1)]
  · refine ⟨fun _ => 1, ?_⟩
    norm_num [quadForm, B, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.hadamard_apply, Matrix.one_apply]

end NLAlib
