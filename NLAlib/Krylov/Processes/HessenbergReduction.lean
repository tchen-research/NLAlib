import NLAlib.Matrix.Factorizations.Hessenberg
import NLAlib.Krylov.Processes.ArnoldiProcess
/-!
# The Arnoldi basis in an unreduced Hessenberg reduction

The columns of an orthogonal Hessenberg reduction form the graded Krylov
basis whenever the Hessenberg factor is unreduced. Positive subdiagonal
normalization identifies it with the canonical Arnoldi process.

Sources: Trefethen–Bau, Lectures 26 and 33; Golub–Van Loan, §7.4.3.
Atlas: `hessenberg-reduction`.
-/
noncomputable section
open Matrix Finset
namespace NLAlib

variable {n : ℕ} {A Q H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

/-- An unreduced Hessenberg intertwining forces column `j` into the first
`j+1` Krylov space. This is the converse direction to Arnoldi's Hessenberg
relation and uses only nonzero subdiagonal entries. -/
theorem col_mem_krylovSpace_of_hessenberg_intertwines
    (hH : IsUnreducedHessenberg H) (hcomm : A * Q = Q * H)
    (j : Fin (n + 1)) : Q.col j ∈ krylovSpace A (Q.col 0) (j + 1) := by
  have hcols : ∀ k : ℕ, ∀ j : Fin (n + 1), j.val = k →
      Q.col j ∈ krylovSpace A (Q.col 0) (j + 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro j hj
      by_cases hk : k = 0
      · have hj0 : j = 0 := Fin.ext (hj.trans hk)
        subst j
        exact self_mem_krylovSpace_succ A (Q.col 0) 0
      · let p : Fin (n + 1) := ⟨k - 1, by omega⟩
        have hpj : (p : ℕ) + 1 = j := by dsimp [p]; omega
        have hprev := ih (k - 1) (by omega) p rfl
        have hA : A *ᵥ Q.col p ∈ krylovSpace A (Q.col 0) (j + 1) := by
          have ha := mulVec_mem_krylovSpace_succ A (Q.col 0) hprev
          rwa [hpj] at ha
        have hrest : (∑ a ∈ univ.erase j, H a p • Q.col a) ∈
            krylovSpace A (Q.col 0) (j + 1) := by
          apply Submodule.sum_mem
          intro a ha
          have haj : a ≠ j := (mem_erase.mp ha).1
          by_cases hak : a.val < k
          · exact Submodule.smul_mem _ _
              (krylovSpace_mono A (Q.col 0) (by omega) (ih a.val hak a rfl))
          · have hzero : H a p = 0 := hH.1 a p (by
              have hne : a.val ≠ j.val := fun h => haj (Fin.ext h)
              dsimp [p]
              omega)
            rw [hzero, zero_smul]
            exact Submodule.zero_mem _
        have hcol : A *ᵥ Q.col p = ∑ a, H a p • Q.col a := by
          calc
            _ = (A * Q).col p := (col_mul_eq_mulVec_col A Q p).symm
            _ = (Q * H).col p := congrArg (fun M => M.col p) hcomm
            _ = _ := by ext i; simp [Matrix.mul_apply, Matrix.col, Finset.sum_apply,
                Pi.smul_apply, smul_eq_mul, mul_comm]
        have hscaled : H j p • Q.col j ∈ krylovSpace A (Q.col 0) (j + 1) := by
          have hsum : H j p • Q.col j + (∑ a ∈ univ.erase j, H a p • Q.col a) =
              A *ᵥ Q.col p := by
            rw [hcol]
            exact add_sum_erase univ (fun a => H a p • Q.col a) (mem_univ j)
          have heq : H j p • Q.col j = A *ᵥ Q.col p -
              (∑ a ∈ univ.erase j, H a p • Q.col a) := eq_sub_iff_add_eq.mpr hsum
          rw [heq]
          exact Submodule.sub_mem _ hA hrest
        have hne : H j p ≠ 0 := hH.2 j p (by omega)
        convert Submodule.smul_mem (krylovSpace A (Q.col 0) (j + 1)) (H j p)⁻¹ hscaled
          using 1
        simp [smul_smul, hne]
  exact hcols j.val j rfl

/-- The full orthogonal factor in an unreduced Hessenberg reduction is an
Arnoldi graded basis, including all prefix-span identities.
atlas: hessenberg-reduction (partial) -/
theorem IsHessenbergForm.isGradedKrylovBasis (h : IsHessenbergForm A Q H)
    (hH : IsUnreducedHessenberg H) : IsGradedKrylovBasis A (Q.col 0) Q := by
  apply IsGradedKrylovBasis.of_mem h.orth
  apply col_mem_krylovSpace_of_hessenberg_intertwines hH
  rw [h.eq, Matrix.mul_assoc, show Qᵀ * Q = 1 from h.orth, Matrix.mul_one]

/-- Under the usual positive-subdiagonal convention, the orthogonal factor
of a Hessenberg reduction is exactly the canonical Arnoldi matrix. Before
normalization the preceding graded-basis theorem identifies its columns up
to signs by `ArnoldiDecomp.exists_sign`.
atlas: hessenberg-reduction (partial) -/
theorem IsHessenbergForm.eq_arnoldiMatrix (h : IsHessenbergForm A Q H)
    (hH : IsUnreducedHessenberg H)
    (hpos : ∀ j (hj : j + 1 < n + 1), 0 < H ⟨j + 1, hj⟩ ⟨j, by omega⟩) :
    Q = arnoldiMatrix A (Q.col 0) (n + 1) := by
  let D : ArnoldiDecomp A (Q.col 0) (n + 1) := ⟨Q, h.isGradedKrylovBasis hH⟩
  apply D.Q_eq_arnoldiMatrix
  · intro hn
    change 0 < Q.col ⟨0, hn⟩ ⬝ᵥ Q.col 0
    simpa using (show (0 : ℝ) < 1 by norm_num)
      |>.trans_le (by rw [h.orth.col_dotProduct_col]; simp)
  · intro j hj
    change 0 < (Qᵀ * A * Q) ⟨j + 1, hj⟩ ⟨j, by omega⟩
    rw [h.transpose_mul_mul_eq]
    exact hpos j hj

end NLAlib
