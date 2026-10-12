import NLAlib.Matrix.Spectral.RealInvariantPlane
import NLAlib.ForMathlib.Analysis.OrthonormalSum
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Real invariant subspaces of dimension one or two

The real and imaginary eigenvector construction transported to arbitrary
finite-dimensional real inner-product spaces.
-/

noncomputable section
open Module
open scoped InnerProductSpace Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- A real endomorphism in positive finite dimension has an eigenline or
an independent pair on which it acts as a nonreal conjugate pair.
Horn–Johnson 2013, Theorem 2.3.1; real Schur deflation helper. -/
theorem exists_real_eigenline_or_plane {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] (T : Module.End ℝ E) :
    (∃ a : ℝ, ∃ u : E, u ≠ 0 ∧ T u = a • u) ∨
    (∃ a b : ℝ, b ≠ 0 ∧ ∃ u v : E,
      LinearIndependent ℝ ![u, v] ∧
      T u = a • u - b • v ∧ T v = b • u + a • v) := by
  classical
  let c := (stdOrthonormalBasis ℝ E).toBasis
  let e := c.equivFun
  let M := T.toMatrix c c
  have : Nonempty (Fin (finrank ℝ E)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  have he (x : Fin (finrank ℝ E) → ℝ) : T (e.symm x) = e.symm (M *ᵥ x) := by
    apply e.injective
    rw [e.apply_symm_apply]
    have h := T.toMatrix_mulVec_repr c c (e.symm x)
    simpa only [← Basis.equivFun_apply, e, LinearEquiv.apply_symm_apply, M] using h.symm
  rcases exists_real_eigenvector_or_invariant_plane M with ⟨a, u, hu, hMu⟩ |
      ⟨a, b, hb, X, hX, hMX⟩
  · left
    refine ⟨a, e.symm u, fun h => hu (e.symm.injective (h.trans e.symm.map_zero.symm)), ?_⟩
    rw [he, hMu, map_smul]
  · right
    have hMu : M *ᵥ X.col 0 = a • X.col 0 - b • X.col 1 := by
      ext i
      have h := congrArg (fun N : Matrix (Fin (finrank ℝ E)) (Fin 2) ℝ => N i 0) hMX
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.col_apply, mul_comm, sub_eq_add_neg] using h
    have hMv : M *ᵥ X.col 1 = b • X.col 0 + a • X.col 1 := by
      ext i
      have h := congrArg (fun N : Matrix (Fin (finrank ℝ E)) (Fin 2) ℝ => N i 1) hMX
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.col_apply, mul_comm] using h
    refine ⟨a, b, hb, e.symm (X.col 0), e.symm (X.col 1), ?_, ?_, ?_⟩
    · have h := hX.map' e.symm.toLinearMap e.symm.ker
      have hvec : (fun i => e.symm (X.col i)) = ![e.symm (X.col 0), e.symm (X.col 1)] := by
        funext i; fin_cases i <;> rfl
      simpa only [LinearEquiv.coe_coe, Function.comp_def, hvec] using h
    · rw [he, hMu, map_sub, map_smul, map_smul]
    · rw [he, hMv, map_add, map_smul, map_smul]

/-- A nonzero real endomorphism space contains an invariant subspace of
dimension one or two. The statement concerns the ambient dimension and
allows the zero endomorphism. Horn–Johnson 2013, Theorem 2.3.1;
real Schur deflation helper. -/
theorem exists_invariant_subspace_finrank_one_or_two {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] (T : Module.End ℝ E) :
    ∃ P : Submodule ℝ E, (finrank ℝ P = 1 ∨ finrank ℝ P = 2) ∧
      ∀ x ∈ P, T x ∈ P := by
  rcases exists_real_eigenline_or_plane T with ⟨a, u, hu, hTu⟩ |
      ⟨a, b, _, u, v, huv, hTu, hTv⟩
  · refine ⟨ℝ ∙ u, Or.inl (finrank_span_singleton hu), ?_⟩
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hTu]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · let P := Submodule.span ℝ (Set.range ![u, v])
    have hu : u ∈ P := Submodule.subset_span ⟨0, rfl⟩
    have hv : v ∈ P := Submodule.subset_span ⟨1, rfl⟩
    refine ⟨P, Or.inr (by simpa [P] using finrank_span_eq_card huv), ?_⟩
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

end NLAlib
