import NLAlib.Matrix.Spectral.RealSchur
import NLAlib.Matrix.Spectral.QuasiPencilBasis
import NLAlib.ForMathlib.Analysis.OrthonormalCons
/-!
# Orthonormal bases for the real generalized Schur form

For an injective second map, real Schur followed by QR gives the full
quasitriangular/triangular pencil form. Otherwise a kernel line is removed
and the construction recurses on its two orthogonal complements.
Source: Horn–Johnson (2013), Theorem 2.6.2.
-/

noncomputable section
open Module
open scoped Matrix InnerProductSpace

namespace NLAlib

/-- Every real square pencil has two orthonormal bases in which the first
factor is upper quasitriangular and the second is upper triangular. Source:
Horn–Johnson (2013), Theorem 2.6.2; singular and identically singular pencils,
common zero images and dimension zero are included. -/
theorem exists_orthonormalBases_real_pencil_upper_quasi_triangular
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (k : ℕ) (A B : E →ₗ[ℝ] F) (hE : finrank ℝ E = k) (hF : finrank ℝ F = k) :
    ∃ (e : OrthonormalBasis (Fin k) ℝ E) (f : OrthonormalBasis (Fin k) ℝ F),
      IsUpperQuasiTriangular (A.toMatrix e.toBasis f.toBasis) ∧
      (B.toMatrix e.toBasis f.toBasis).IsUpperTriangular := by
  classical
  induction k generalizing E F with
  | zero =>
    let e := (stdOrthonormalBasis ℝ E).reindex (finCongr hE)
    let f := (stdOrthonormalBasis ℝ F).reindex (finCongr hF)
    exact ⟨e, f, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, fun {i} => Fin.elim0 i⟩
  | succ k ih =>
    by_cases hB : Function.Injective B
    · let bEquiv := B.linearEquivOfInjective hB (hE.trans hF.symm)
      let T : Module.End ℝ E := bEquiv.symm.toLinearMap.comp A
      obtain ⟨e, he⟩ := exists_orthonormalBasis_upper_quasi_triangular (k + 1) T hE
      obtain ⟨f, hAf, hBf⟩ := exists_orthonormalBasis_pencil_of_quasi_basis A bEquiv e hF he
      exact ⟨e, f, hAf, hBf⟩
    · have : Nontrivial E := finrank_pos_iff.mp (by rw [hE]; omega)
      have : Nontrivial F := finrank_pos_iff.mp (by rw [hF]; omega)
      obtain ⟨u, v, a, hu, hv, hAu, hBu⟩ := exists_unit_pencil_image_line_of_not_injective A B hB
      have hu0 : u ≠ 0 := by intro h; simp [h] at hu
      have hv0 : v ≠ 0 := by intro h; simp [h] at hv
      let E' : Submodule ℝ E := (ℝ ∙ u)ᗮ
      let F' : Submodule ℝ F := (ℝ ∙ v)ᗮ
      have hE' : finrank ℝ E' = k := by
        have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
        rw [finrank_span_singleton hu0, hE] at h
        dsimp [E']
        omega
      have hF' : finrank ℝ F' = k := by
        have h := (ℝ ∙ v).finrank_add_finrank_orthogonal
        rw [finrank_span_singleton hv0, hF] at h
        dsimp [F']
        omega
      let comp (L : E →ₗ[ℝ] F) : E' →ₗ[ℝ] F' :=
        F'.orthogonalProjectionOnto.toLinearMap.comp (L.comp E'.subtype)
      obtain ⟨e', f', hA', hB'⟩ := ih (comp A) (comp B) hE' hF'
      obtain ⟨e, he0, heS⟩ := exists_orthonormalBasis_cons hE u hu e'
      obtain ⟨f, hf0, hfS⟩ := exists_orthonormalBasis_cons hF v hv f'
      have hcol (L : E →ₗ[ℝ] F) (c : ℝ) (hLu : L u = c • v) (i : Fin k) :
          L.toMatrix e.toBasis f.toBasis i.succ 0 = 0 := by
        simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply, he0, hLu,
          hfS, inner_smul_right]
        have hinner : inner ℝ (f' i : F) v = 0 :=
          Submodule.mem_orthogonal_singleton_iff_inner_left.mp (f' i).property
        rw [hinner, mul_zero]
      have htail (L : E →ₗ[ℝ] F) :
          (L.toMatrix e.toBasis f.toBasis).submatrix Fin.succ Fin.succ =
            (comp L).toMatrix e'.toBasis f'.toBasis := by
        ext i j
        simp only [Matrix.submatrix_apply, LinearMap.toMatrix_apply,
          OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
          OrthonormalBasis.repr_apply_apply, heS, hfS, comp, LinearMap.comp_apply,
          ContinuousLinearMap.coe_coe, Submodule.subtype_apply,
          Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
      refine ⟨e, f, isUpperQuasiTriangular_of_first_column_and_tail
        (hcol A a hAu) (by rw [htail]; exact hA'), ?_⟩
      intro i j hij
      revert hij
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        have hi : i ≠ 0 := ne_of_gt hij
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
        exact hcol B 0 (by simpa only [zero_smul] using hBu) i
      · refine Fin.cases ?_ (fun i => ?_) i
        · intro h; exact (not_lt_of_ge (Fin.zero_le _)) h |>.elim
        · intro h
          change ((B.toMatrix e.toBasis f.toBasis).submatrix Fin.succ Fin.succ) i j = 0
          rw [htail]
          exact hB' (Fin.succ_lt_succ_iff.mp h)

end NLAlib
