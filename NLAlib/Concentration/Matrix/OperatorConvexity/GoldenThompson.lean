import NLAlib.Concentration.Matrix.OperatorConvexity.LiebConcavity
import NLAlib.Concentration.Matrix.OperatorConvexity.UnitaryCalculus
import NLAlib.Concentration.Matrix.Laplace.CgfExpLog
import NLAlib.Matrix.CoordinatePinching

/-!
# Golden–Thompson via finite pinching

Lieb concavity increases `traceExp (H + matrixLog X)` under coordinate
pinching in an eigenbasis of `H`. After all coordinates are pinched, the
diagonal calculation gives `trace (matrixExp H * X)`. Substitution
`X = matrixExp K` proves Golden–Thompson without a limiting argument.

Source: Bhatia 1997, Chapter IX.3; the finite pinching derivation in
`Re-derivations/matrix_toolkit_operator_derivations.tex`, §7.
Atlas: `golden-thompson`.
-/

noncomputable section
set_option autoImplicit false

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib
open Matrix

private theorem diagonal_real_isHermitian {ι : Type*} [DecidableEq ι] (h : ι → ℝ) :
    (diagonal fun i => (h i : ℂ)).IsHermitian := by
  exact isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)

private theorem matrixExp_diagonal_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℝ) :
    matrixExp (diagonal fun i => (h i : ℂ)) =
      diagonal fun i => (Real.exp (h i) : ℂ) := by
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp (diagonal_real_isHermitian h)]
  exact cfc_diagonal_real Real.exp h

private theorem traceExp_add_matrixLog_coordinatePinch {d : ℕ} [NeZero d]
    (h : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosDef) (k : Fin d) :
    (coordinatePinch k X).PosDef ∧
      traceExp (diagonal (fun i => (h i : ℂ)) + matrixLog X) ≤
        traceExp (diagonal (fun i => (h i : ℂ)) + matrixLog (coordinatePinch k X)) := by
  let H := diagonal fun i => (h i : ℂ)
  let R := coordinateReflection k
  have hR : Rᴴ = R := conjTranspose_coordinateReflection k
  have hR2 : R * R = 1 := coordinateReflection_mul_self k
  have hRX : (R * X * R).PosDef := (posDef_reflection_conj_iff R X hR hR2).2 hX
  have hc := lieb_concavity H (diagonal_real_isHermitian h)
  have hp := hc.1 hX hRX (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have he := hc.2 hX hRX (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hinv := traceExp_add_matrixLog_reflection_conj_of_conj_eq R H X hR hR2
    hX.isHermitian (coordinateReflection_mul_diagonal_mul k _)
  change (coordinatePinch k X).PosDef at hp
  change (1 / 2 : ℝ) * traceExp (H + matrixLog X) +
    (1 / 2 : ℝ) * traceExp (H + matrixLog (R * X * R)) ≤
      traceExp (H + matrixLog (coordinatePinch k X)) at he
  rw [hinv] at he
  refine ⟨hp, ?_⟩
  change traceExp (H + matrixLog X) ≤ _
  linarith

private theorem traceExp_add_matrixLog_coordinatePinched {d : ℕ} [NeZero d]
    (h : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosDef)
    (s : Finset (Fin d)) :
    (coordinatePinched s X).PosDef ∧
      traceExp (diagonal (fun i => (h i : ℂ)) + matrixLog X) ≤
        traceExp (diagonal (fun i => (h i : ℂ)) + matrixLog (coordinatePinched s X)) := by
  induction s using Finset.induction_on with
  | empty => simpa using And.intro hX (le_refl (traceExp
      (diagonal (fun i => (h i : ℂ)) + matrixLog X)))
  | @insert k s _ ih =>
    rw [coordinatePinched_insert]
    obtain ⟨hp, he⟩ := traceExp_add_matrixLog_coordinatePinch h _ ih.1 k
    exact ⟨hp, ih.2.trans he⟩

private theorem traceExp_add_matrixLog_diagonal_endpoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℝ) (X : Matrix ι ι ℂ) (hX : X.PosDef) :
    traceExp (diagonal (fun i => (h i : ℂ)) + matrixLog (diagonal fun i => X i i)) =
      (Matrix.trace (matrixExp (diagonal fun i => (h i : ℂ)) * X)).re := by
  have hr (i : ι) : ((X i i).re : ℂ) = X i i := by
    exact Complex.conj_eq_iff_re.mp (hX.isHermitian.apply i i)
  have hx (i : ι) : 0 < (X i i).re := (Complex.pos_iff.mp hX.diag_pos).1
  have hd : diagonal (fun i => X i i) = diagonal (fun i => ((X i i).re : ℂ)) := by
    congr 1
    exact (funext hr).symm
  have hl : matrixLog (diagonal fun i => X i i) =
      diagonal (fun i => (Real.log (X i i).re : ℂ)) := by
    rw [hd, matrixLog, cfc_diagonal_real]
  unfold traceExp
  rw [hl, diagonal_add]
  simp only [← Complex.ofReal_add]
  rw [matrixExp_diagonal_real, matrixExp_diagonal_real]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_apply_eq,
    Matrix.diagonal_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Real.exp_add, Real.exp_log (hx i)]

/-- In an eigenbasis of the Hermitian parameter, finite midpoint pinching bounds
the Lieb trace function by its diagonal trace pairing. Source: Bhatia 1997,
IX.3; operator derivations §7. Atlas `golden-thompson` (diagonal helper). -/
theorem traceExp_add_matrixLog_diagonal_le {d : ℕ} [NeZero d]
    (h : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosDef) :
    traceExp (diagonal (fun i => (h i : ℂ)) + matrixLog X) ≤
      (Matrix.trace (matrixExp (diagonal fun i => (h i : ℂ)) * X)).re := by
  have hp := (traceExp_add_matrixLog_coordinatePinched h X hX Finset.univ).2
  rw [coordinatePinched_univ, traceExp_add_matrixLog_diagonal_endpoint h X hX] at hp
  exact hp

/-- The positive-definite form of Golden–Thompson: the Lieb trace function is at
most the trace pairing with `exp H`. Source: Bhatia 1997, IX.3; finite pinching
proof in operator derivations §7. Atlas `golden-thompson` (equivalent variant). -/
theorem traceExp_add_matrixLog_le_fin {d : ℕ} [NeZero d]
    (H X : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) (hX : X.PosDef) :
    traceExp (H + matrixLog X) ≤ (Matrix.trace (matrixExp H * X)).re := by
  let U := star hH.eigenvectorUnitary
  have hD : (U : Matrix (Fin d) (Fin d) ℂ) * H * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ =
      diagonal (fun i => (hH.eigenvalues i : ℂ)) :=
    hH.conjStarAlgAut_star_eigenvectorUnitary
  have hp := traceExp_add_matrixLog_diagonal_le hH.eigenvalues
    ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)
    ((posDef_unitary_conj_iff U X).2 hX)
  rw [← hD, traceExp_add_matrixLog_unitary_conj U H X hX.isHermitian,
    re_trace_matrixExp_mul_unitary_conj U H X] at hp
  exact hp

/-- Golden–Thompson for two complex Hermitian matrices on a nonempty `Fin` index.
Source: Bhatia 1997, IX.3; operator derivations §7. Atlas `golden-thompson`
(finite-dimensional helper for the arbitrary-index theorem). -/
theorem golden_thompson_fin {d : ℕ} [NeZero d]
    (H K : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    traceExp (H + K) ≤ (Matrix.trace (matrixExp H * matrixExp K)).re := by
  obtain ⟨hX, hlog⟩ := posDef_matrixExp_and_matrixLog_matrixExp K hK
  simpa only [hlog] using traceExp_add_matrixLog_le_fin H (matrixExp K) hH hX

/-- Golden–Thompson: `tr exp(H + K) ≤ tr(exp H · exp K)` for complex Hermitian
matrices with any finite index type, including the empty matrix. The ordered
scalar traces are represented by their real parts. Source: Bhatia 1997, IX.3;
finite pinching proof in operator derivations §7.
atlas: golden-thompson -/
theorem golden_thompson {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H K : Matrix ι ι ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    traceExp (H + K) ≤ (Matrix.trace (matrixExp H * matrixExp K)).re := by
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    let := hi
    simp [traceExp, Matrix.trace]
  | inr hi =>
    let := hi
    let e := Fintype.equivFin ι
    let E := reindexStarAlgEquiv e
    have hf := golden_thompson_fin (E H) (E K) (hH.reindex e) (hK.reindex e)
    have ha : E H + E K = E (H + K) := (map_add E H K).symm
    have he : matrixExp (E H) = E (matrixExp H) := matrixExp_reindex e H
    have heK : matrixExp (E K) = E (matrixExp K) := matrixExp_reindex e K
    rw [ha, he, heK, ← map_mul E] at hf
    change traceExp (Matrix.reindex e e (H + K)) ≤
      (Matrix.trace (Matrix.reindex e e (matrixExp H * matrixExp K))).re at hf
    simpa only [traceExp_reindex, trace_reindex] using hf

private theorem trace_mul_im_eq_zero_of_isHermitian {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).im = 0 := by
  have hs : star (Matrix.trace (A * B)) = Matrix.trace (A * B) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hB.eq, hA.eq,
      Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.mp hs

/-- Golden–Thompson stated directly with the complex traces. Both traces are
real; `ComplexOrder` compares their real values and retains equality of their
imaginary parts. Source: Bhatia 1997, IX.3; operator derivations §7.
atlas: golden-thompson -/
theorem golden_thompson_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H K : Matrix ι ι ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    Matrix.trace (matrixExp (H + K)) ≤ Matrix.trace (matrixExp H * matrixExp K) := by
  apply Complex.le_def.mpr
  refine ⟨golden_thompson H K hH hK, ?_⟩
  have hleft : (Matrix.trace (matrixExp (H + K))).im = 0 := by
    have he : (matrixExp (H + K)).IsHermitian := (hH.add hK).exp
    have hs : star (Matrix.trace (matrixExp (H + K))) =
        Matrix.trace (matrixExp (H + K)) := by
      rw [← Matrix.trace_conjTranspose, he.eq]
    exact Complex.conj_eq_iff_im.mp hs
  exact hleft.trans (trace_mul_im_eq_zero_of_isHermitian _ _ hH.exp hK.exp).symm

/-- The positive-definite form of Golden–Thompson on arbitrary finite index
types: `tr exp(H + log X) ≤ tr(exp H · X)`. Only `H` is Hermitian and `X` is
positive definite; empty matrices are included. Source: Bhatia 1997, IX.3;
operator derivations §7 (equivalent variant).
atlas: golden-thompson -/
theorem traceExp_add_matrixLog_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H X : Matrix ι ι ℂ) (hH : H.IsHermitian) (hX : X.PosDef) :
    traceExp (H + matrixLog X) ≤ (Matrix.trace (matrixExp H * X)).re := by
  have hl : (matrixLog X).IsHermitian := cfc_predicate Real.log X
  have he : matrixExp (matrixLog X) = X := CFC.exp_log X hX.isStrictlyPositive
  simpa only [he] using golden_thompson H (matrixLog X) hH hl

end NLAlib
