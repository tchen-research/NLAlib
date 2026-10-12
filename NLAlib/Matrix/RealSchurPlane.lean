import NLAlib.Matrix.RealInvariantSubspace
import NLAlib.Matrix.RealPlaneSchur
import NLAlib.Matrix.OrthogonalBasisChange

/-!
# Canonical real invariant Schur planes

A real invariant plane carrying a nonreal conjugate pair has an orthonormal
basis with equal diagonal entries and strictly negative off-diagonal product.
-/

noncomputable section
open Module
open scoped InnerProductSpace Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Equal diagonal entries and the characteristic polynomial of a nonreal
conjugate pair force the corrected real Schur block shape and negative
off-diagonal product. Horn–Johnson 2013, Theorem 2.3.1. -/
theorem eq_real_schur_block_of_charpoly {A : Matrix (Fin 2) (Fin 2) ℝ}
    {a b : ℝ} (hb : b ≠ 0) (hdiag : A 0 0 = A 1 1)
    (hchar : A.charpoly = (!![a, b; -b, a] : Matrix (Fin 2) (Fin 2) ℝ).charpoly) :
    A = !![a, A 0 1; A 1 0, a] ∧ A 0 1 * A 1 0 < 0 := by
  have ht : A 0 0 + A 1 1 = a + a := by
    have h := congrArg (fun p : Polynomial ℝ => p.coeff 1) hchar
    simp only [Matrix.charpoly_fin_two] at h
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at h
    linarith
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = a * a + b * b := by
    have h := congrArg (fun p : Polynomial ℝ => p.coeff 0) hchar
    simpa [Matrix.charpoly_fin_two, Matrix.det_fin_two] using h
  have ha0 : A 0 0 = a := by linarith
  have ha1 : A 1 1 = a := by linarith
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [ha0, ha1]
  · rw [ha0, ha1] at hd
    nlinarith [sq_pos_of_ne_zero hb]

/-- A two-dimensional operator whose matrix in some basis is a nonreal
rotation-dilation block has an orthonormal basis with corrected real Schur
block `[[a,c],[d,a]]`, where `cd<0`. No normality is assumed.
Horn–Johnson 2013, Theorem 2.3.1; derivations equation (G1). -/
theorem exists_orthonormalBasis_real_schur_plane {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : Module.End ℝ E) (d : Basis (Fin 2) ℝ E) (a b : ℝ) (hb : b ≠ 0)
    (hT : T.toMatrix d d = !![a, b; -b, a]) :
    ∃ c : OrthonormalBasis (Fin 2) ℝ E, ∃ s t : ℝ,
      T.toMatrix c.toBasis c.toBasis = !![a, s; t, a] ∧ s * t < 0 := by
  have hdim : finrank ℝ E = 2 := by simpa using finrank_eq_card_basis d
  let c₀ := (stdOrthonormalBasis ℝ E).reindex (finCongr hdim)
  obtain ⟨Q, hQ, hdiag⟩ := exists_orthogonal_two_eq_diagonal (T.toMatrix c₀.toBasis c₀.toBasis)
  obtain ⟨c, hc⟩ := exists_orthonormalBasis_toMatrix_eq_conjugate c₀ Q hQ
  have hdiag' : (T.toMatrix c.toBasis c.toBasis) 0 0 =
      (T.toMatrix c.toBasis c.toBasis) 1 1 := by rw [hc T]; exact hdiag
  have hchar : (T.toMatrix c.toBasis c.toBasis).charpoly =
      (!![a, b; -b, a] : Matrix (Fin 2) (Fin 2) ℝ).charpoly := by
    rw [T.charpoly_toMatrix, ← T.charpoly_toMatrix d, hT]
  obtain ⟨heq, hneg⟩ := eq_real_schur_block_of_charpoly hb hdiag' hchar
  exact ⟨c, _, _, heq, hneg⟩

/-- Every real endomorphism in positive dimension has an invariant real
line, or an invariant real plane with a canonical orthonormal Schur block.
Horn–Johnson 2013, Theorem 2.3.1; corrected real Schur deflation step. -/
theorem exists_invariant_line_or_real_schur_plane {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] (T : Module.End ℝ E) :
    (∃ P : Submodule ℝ E, finrank ℝ P = 1 ∧ ∀ x ∈ P, T x ∈ P) ∨
    (∃ P : Submodule ℝ E, ∃ hP : ∀ x ∈ P, T x ∈ P,
      ∃ c : OrthonormalBasis (Fin 2) ℝ P, ∃ a s t : ℝ,
        (T.restrict hP).toMatrix c.toBasis c.toBasis = !![a, s; t, a] ∧ s * t < 0) := by
  classical
  rcases exists_real_eigenline_or_plane T with ⟨a, u, hu, hTu⟩ |
      ⟨a, b, hb, u, v, huv, hTu, hTv⟩
  · left
    refine ⟨ℝ ∙ u, finrank_span_singleton hu, ?_⟩
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hTu]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · right
    let P := Submodule.span ℝ (Set.range ![u, v])
    have hu : u ∈ P := Submodule.subset_span ⟨0, rfl⟩
    have hv : v ∈ P := Submodule.subset_span ⟨1, rfl⟩
    have hP : ∀ x ∈ P, T x ∈ P := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        fin_cases i
        · change T u ∈ P
          rw [hTu]
          exact P.sub_mem (P.smul_mem _ hu) (P.smul_mem _ hv)
        · change T v ∈ P
          rw [hTv]
          exact P.add_mem (P.smul_mem _ hu) (P.smul_mem _ hv)
      | zero => simpa only [map_zero] using P.zero_mem
      | add x y _ _ hx hy => simpa only [map_add] using P.add_mem hx hy
      | smul c x _ hx => simpa only [map_smul] using P.smul_mem c hx
    let d : Basis (Fin 2) ℝ P := Basis.span huv
    have hd0' : (d 0 : E) = u := Basis.coe_span_apply huv 0
    have hd1' : (d 1 : E) = v := Basis.coe_span_apply huv 1
    have hd0 : T.restrict hP (d 0) = a • d 0 - b • d 1 := by
      apply Subtype.ext
      change T (d 0 : E) = a • (d 0 : E) - b • (d 1 : E)
      rwa [hd0', hd1']
    have hd1 : T.restrict hP (d 1) = b • d 0 + a • d 1 := by
      apply Subtype.ext
      change T (d 1 : E) = b • (d 0 : E) + a • (d 1 : E)
      rwa [hd0', hd1']
    have hmat : (T.restrict hP).toMatrix d d = !![a, b; -b, a] := by
      ext i j
      fin_cases j <;> fin_cases i <;>
        simp [LinearMap.toMatrix_apply, hd0, hd1]
    obtain ⟨c, s, t, hct, hst⟩ := exists_orthonormalBasis_real_schur_plane (T.restrict hP) d a b hb hmat
    exact ⟨P, hP, c, a, s, t, hct, hst⟩

end NLAlib
