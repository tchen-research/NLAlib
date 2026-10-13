import NLAlib.Matrix.Spectral.SingularValueSpectrum

/-!
# Ordered eigenvalues of matrix functional calculus

A scalar function that keeps the decreasing order of a finite Hermitian spectrum acts
entrywise on the sorted eigenvalue list `eigenvalues₀` (`eigenvalues₀_cfc_of_antitone`); applied
to `x ↦ x²` this identifies the singular values of a PSD matrix with its sorted eigenvalues
(`singularValues_eq_eigenvalues₀_of_posSemidef`). Over `[RCLike 𝕜]`. Horn–Johnson 2013,
Thm 2.5.6 and §7.3; supports `condition-number-def` and the nuclear-norm trace identities.
-/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib

set_option backward.isDefEq.respectTransparency false

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- If `i ↦ f(λᵢ)` is decreasing along the sorted eigenvalues of the Hermitian `A`, then the
sorted eigenvalues of `f(A)` are `f(λᵢ)`, with multiplicities. Horn–Johnson 2013, Thm 2.5.6;
supports `condition-number-def`. -/
theorem eigenvalues₀_cfc_of_antitone (f : ℝ → ℝ) {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hf : Antitone (fun i => f (hA.eigenvalues₀ i)))
    (i : Fin (Fintype.card n)) :
    (show (cfc f A).IsHermitian from cfc_predicate f A).eigenvalues₀ i = f (hA.eigenvalues₀ i) := by
  have hC : (cfc f A).IsHermitian := cfc_predicate f A
  have hMult : Finset.univ.val.map hA.eigenvalues = Finset.univ.val.map hA.eigenvalues₀ := by
    have h := congrArg (Multiset.map (RCLike.re : 𝕜 → ℝ))
      (hA.roots_charpoly_eq_eigenvalues.symm.trans hA.roots_charpoly_eq_eigenvalues₀)
    simpa [Multiset.map_map, Function.comp_def] using h
  have hRoots : (cfc f A).charpoly.roots =
      Finset.univ.val.map (fun j => (f (hA.eigenvalues₀ j) : 𝕜)) := by
    rw [hA.charpoly_cfc_eq f, Polynomial.roots_prod]
    · simpa [Multiset.map_map, Function.comp_def] using
        congrArg (Multiset.map (fun x : ℝ => (f x : 𝕜))) hMult
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hList : List.ofFn hC.eigenvalues₀ = List.ofFn (fun j => f (hA.eigenvalues₀ j)) := by
    rw [← hC.sort_roots_charpoly_eq_eigenvalues₀, hRoots]
    simp only [Function.comp_def, RCLike.ofReal_re, Fin.univ_val_map,
      Multiset.map_coe, List.map_ofFn, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simpa only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using hf.sortedGE_ofFn
  exact congrFun (List.ofFn_inj.mp hList) i

/-- The singular values of a PSD matrix are its sorted eigenvalues, at every index below the
dimension (zeros and repeated values included). Horn–Johnson 2013, Thm 7.3.1; supports
`condition-number-def`. -/
theorem singularValues_eq_eigenvalues₀_of_posSemidef
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (i : Fin (Fintype.card n)) :
    singularValues A (i : ℕ) = hA.isHermitian.eigenvalues₀ i := by
  have hNonneg (j : Fin (Fintype.card n)) : 0 ≤ hA.isHermitian.eigenvalues₀ j := by
    let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
    have h := hA.eigenvalues_nonneg (e j)
    simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using h
  have hAnti : Antitone (fun j => hA.isHermitian.eigenvalues₀ j ^ 2) := by
    intro j k hjk
    exact pow_le_pow_left₀ (hNonneg k) (hA.isHermitian.eigenvalues₀_antitone hjk) 2
  have hCfc : cfc (fun x : ℝ => x ^ (2 : ℕ)) A = Aᴴ * A := by
    calc
      cfc (fun x : ℝ => x ^ (2 : ℕ)) A = A ^ 2 := cfc_pow_id (R := ℝ) A 2 hA.isHermitian
      _ = Aᴴ * A := by rw [pow_two, hA.isHermitian.eq]
  have hE := eigenvalues₀_cfc_of_antitone (fun x : ℝ => x ^ (2 : ℕ)) hA.isHermitian hAnti i
  have hSq := sq_singularValues_eq_eigenvalues₀ A i
  have h : (singularValues A (i : ℕ)) ^ 2 =
      (hA.isHermitian.eigenvalues₀ i) ^ 2 := hSq.trans
        ((congrFun (eigenvalues₀_eq_of_matrix_eq _ _ hCfc.symm) i).trans hE)
  exact (sq_eq_sq₀ (singularValues_nonneg A _) (hNonneg i)).mp h

end NLAlib
