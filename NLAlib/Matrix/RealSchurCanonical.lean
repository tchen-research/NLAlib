import NLAlib.Matrix.RealSchur
import NLAlib.Matrix.RealSchurPlane

/-!
# The corrected canonical real Schur form

The nonzero subdiagonals identify disjoint two-dimensional blocks. Each has
equal diagonal entries and negative off-diagonal product. The orthogonal
similarity is valid for every real square matrix, without normality.
-/

noncomputable section
open Module
open scoped InnerProductSpace Matrix
namespace NLAlib

/-- A real Schur matrix is upper quasitriangular and each nonscalar block
has shape `[[a,b],[c,a]]` with `bc<0`. The nonzero subdiagonal selects its
two-dimensional blocks. Horn–Johnson 2013, Theorem 2.3.1;
the corrected form in derivations equation (G1). -/
def IsRealSchurForm {k : ℕ} (T : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  IsUpperQuasiTriangular T ∧
    ∀ i j, j.val + 1 = i.val → T i j ≠ 0 → T i i = T j j ∧ T j i * T i j < 0

/-- Joining a scalar or nonreal real Schur block to a real Schur tail gives
a real Schur matrix. Horn–Johnson 2013, Theorem 2.3.1; block induction helper. -/
theorem isRealSchurForm_of_small_leading_block {p q : ℕ}
    {T : Matrix (Fin (p + q)) (Fin (p + q)) ℝ} (hp : p ≤ 2)
    (hzero : ∀ i : Fin q, ∀ j : Fin p, T (Fin.natAdd p i) (Fin.castAdd q j) = 0)
    (hhead : ∀ i j : Fin p, j.val + 1 = i.val →
      T (Fin.castAdd q i) (Fin.castAdd q j) ≠ 0 →
      T (Fin.castAdd q i) (Fin.castAdd q i) = T (Fin.castAdd q j) (Fin.castAdd q j) ∧
      T (Fin.castAdd q j) (Fin.castAdd q i) * T (Fin.castAdd q i) (Fin.castAdd q j) < 0)
    (htail : IsRealSchurForm (T.submatrix (Fin.natAdd p) (Fin.natAdd p))) :
    IsRealSchurForm T := by
  refine ⟨isUpperQuasiTriangular_of_small_leading_block hp hzero htail.1, ?_⟩
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · exact hhead i j
  · intro h; have := i.isLt; simp only [Fin.val_castAdd, Fin.val_natAdd] at h; omega
  · intro _ h; exact (h (hzero i j)).elim
  · intro h hn
    exact htail.2 i j (by simp only [Fin.val_natAdd] at h; omega) hn

/-- Every real endomorphism in positive dimension has an invariant
orthonormal scalar or canonical nonreal Schur block of size at most two.
Horn–Johnson 2013, Theorem 2.3.1; real Schur induction step. -/
theorem exists_small_real_schur_subspace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] (T : Module.End ℝ E) :
    ∃ p : ℕ, 0 < p ∧ p ≤ 2 ∧ ∃ P : Submodule ℝ E,
      ∃ hP : ∀ x ∈ P, T x ∈ P, ∃ b : OrthonormalBasis (Fin p) ℝ P,
        ∀ i j, j.val + 1 = i.val → (T.restrict hP).toMatrix b.toBasis b.toBasis i j ≠ 0 →
          (T.restrict hP).toMatrix b.toBasis b.toBasis i i =
            (T.restrict hP).toMatrix b.toBasis b.toBasis j j ∧
          (T.restrict hP).toMatrix b.toBasis b.toBasis j i *
            (T.restrict hP).toMatrix b.toBasis b.toBasis i j < 0 := by
  rcases exists_invariant_line_or_real_schur_plane T with ⟨P, hdim, hP⟩ |
      ⟨P, hP, b, a, s, t, hmat, hst⟩
  · refine ⟨1, by omega, by omega, P, hP,
      (stdOrthonormalBasis ℝ P).reindex (finCongr hdim), ?_⟩
    intro i j hij
    have := i.isLt
    omega
  · refine ⟨2, by omega, le_rfl, P, hP, b, ?_⟩
    intro i j hij _
    rw [hmat]
    have hi : i = 1 := Fin.ext (by have := i.isLt; omega)
    have hj : j = 0 := Fin.ext (by have := i.isLt; omega)
    subst i; subst j
    exact ⟨rfl, hst⟩

/-- Every real endomorphism has an orthonormal basis in corrected real
Schur form: scalar blocks and nonreal blocks `[[a,b],[c,a]]` with `bc<0`.
Empty dimension is included; normality is not required. Horn–Johnson 2013,
Theorem 2.3.1; derivations equation (G1).
atlas: schur-triangularization (partial) -/
theorem exists_orthonormalBasis_real_schur {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ) (T : Module.End ℝ E) (hk : finrank ℝ E = k) :
    ∃ b : OrthonormalBasis (Fin k) ℝ E,
      IsRealSchurForm (T.toMatrix b.toBasis b.toBasis) := by
  classical
  induction k using Nat.strong_induction_on generalizing E with
  | h k ih =>
    by_cases hk0 : k = 0
    · have : IsEmpty (Fin k) := by rw [hk0]; infer_instance
      exact ⟨(stdOrthonormalBasis ℝ E).reindex (finCongr hk),
        ⟨⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩, fun i => isEmptyElim i⟩⟩
    have : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hk]; omega)
    obtain ⟨p, hp0, hp, P, hP, bP, hhead⟩ := exists_small_real_schur_subspace T
    have hPdim : finrank ℝ P = p := by simpa using finrank_eq_card_basis bP.toBasis
    let q := finrank ℝ Pᗮ
    have hsum : p + q = k := by
      rw [← hPdim]
      exact P.finrank_add_finrank_orthogonal.trans hk
    have hq : q < k := by omega
    let C : Module.End ℝ Pᗮ :=
      Pᗮ.orthogonalProjectionOnto.toLinearMap.comp (T.comp Pᗮ.subtype)
    obtain ⟨bQ, hbQ⟩ := ih q hq C rfl
    obtain ⟨b₀, hbP, hbQ'⟩ := exists_orthonormalBasis_sum P bP bQ
    let b₁ : OrthonormalBasis (Fin (p + q)) ℝ E := b₀.reindex finSumFinEquiv
    have hleft (i : Fin p) : b₁ (Fin.castAdd q i) = (bP i : E) := by
      simpa only [b₁, OrthonormalBasis.reindex_apply,
        finSumFinEquiv_symm_apply_castAdd] using hbP i
    have hright (i : Fin q) : b₁ (Fin.natAdd p i) = (bQ i : E) := by
      simpa only [b₁, OrthonormalBasis.reindex_apply,
        finSumFinEquiv_symm_apply_natAdd] using hbQ' i
    have hhead' (i j : Fin p) :
        (T.toMatrix b₁.toBasis b₁.toBasis) (Fin.castAdd q i) (Fin.castAdd q j) =
          (T.restrict hP).toMatrix bP.toBasis bP.toBasis i j := by
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply, hleft,
        Submodule.coe_inner, LinearMap.restrict_apply]
    have htri : IsRealSchurForm (T.toMatrix b₁.toBasis b₁.toBasis) := by
      apply isRealSchurForm_of_small_leading_block hp
      · intro i j
        simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply, hleft, hright]
        exact Submodule.inner_left_of_mem_orthogonal (hP _ (bP j).property) (bQ i).property
      · simpa only [hhead'] using hhead
      · have heq : (T.toMatrix b₁.toBasis b₁.toBasis).submatrix (Fin.natAdd p) (Fin.natAdd p) =
            C.toMatrix bQ.toBasis bQ.toBasis := by
          ext i j
          simp only [Matrix.submatrix_apply, LinearMap.toMatrix_apply,
            OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
            OrthonormalBasis.repr_apply_apply, hright, C, LinearMap.comp_apply,
            ContinuousLinearMap.coe_coe, Submodule.subtype_apply,
            Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
        rwa [heq]
    let b := b₁.reindex (finCongr hsum)
    refine ⟨b, ⟨?_, ?_⟩, ?_⟩
    · intro i j hij
      simpa only [b, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply,
        OrthonormalBasis.reindex_apply] using htri.1.1 ((finCongr hsum).symm i)
          ((finCongr hsum).symm j) (by simpa using hij)
    · intro i j l hij hjl
      simpa only [b, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply,
        OrthonormalBasis.reindex_apply] using htri.1.2 ((finCongr hsum).symm i)
          ((finCongr hsum).symm j) ((finCongr hsum).symm l)
            (by simpa using hij) (by simpa using hjl)
    · intro i j hij hn
      have h := htri.2 ((finCongr hsum).symm i) ((finCongr hsum).symm j) (by simpa using hij)
      simp only [b, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply,
        OrthonormalBasis.reindex_apply] at hn h ⊢
      exact h hn

end NLAlib
