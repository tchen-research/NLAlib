import NLAlib.ForMathlib.MeasureTheory.PolynomialZeroSets

/-!
# Polynomial zero sets over a normed field

The atomless-product argument also applies to complex polynomials. It uses
only finite root sets and Fubini; no realification or covariance hypothesis
is needed. This extends the proved real argument to normed infinite fields.
-/

noncomputable section
open MeasureTheory
namespace MvPolynomial
variable {𝕜 : Type*} [NormedField 𝕜] [Infinite 𝕜] [SecondCountableTopology 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]
private theorem ae_eval_ne_zero_normedField_fin (μ : Measure 𝕜) [SigmaFinite μ]
    [NullSingletonClass μ] :
    ∀ (n : ℕ) (f : MvPolynomial (Fin n) 𝕜), f ≠ 0 →
      ∀ᵐ x ∂(Measure.pi fun _ : Fin n => μ), MvPolynomial.eval x f ≠ 0 := by
  classical
  intro n
  induction n with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x hx => hf ?_
    apply MvPolynomial.funext
    intro y
    have : y = x := Subsingleton.elim _ _
    subst this
    simpa using hx
  | succ n ih =>
    intro f hf
    set g := MvPolynomial.finSuccEquiv 𝕜 n f with hg
    have hg0 : g ≠ 0 := by
      intro h; apply hf
      exact (MvPolynomial.finSuccEquiv 𝕜 n).injective (by rw [← hg, h, map_zero])
    have hc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
    have hih := ih g.leadingCoeff hc
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0
    let T : Set (𝕜 × (Fin n → 𝕜)) :=
      {q | MvPolynomial.eval (Fin.cons q.1 q.2 : Fin (n+1) → 𝕜) f = 0}
    have hT : MeasurableSet T := by
      have hcont : Continuous fun q : 𝕜 × (Fin n → 𝕜) =>
          MvPolynomial.eval (Fin.cons q.1 q.2 : Fin (n+1) → 𝕜) f := by
        apply (MvPolynomial.continuous_eval f).comp
        refine continuous_pi fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using continuous_fst
        · simp only [Fin.cons_succ]; exact (continuous_apply j).comp continuous_snd
      exact hcont.measurable (measurableSet_singleton 0)
    have hpre : MeasurableEquiv.piFinSuccAbove (fun _ => 𝕜) 0 ⁻¹' T =
        {x | MvPolynomial.eval x f = 0} := by
      ext x
      have hx : (Fin.cons (MeasurableEquiv.piFinSuccAbove (fun _ => 𝕜) 0 x).1
          (MeasurableEquiv.piFinSuccAbove (fun _ => 𝕜) 0 x).2 : Fin (n+1) → 𝕜) = x := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [MeasurableEquiv.piFinSuccAbove_apply]
        · simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
      simp only [Set.mem_preimage, T, Set.mem_ofPred_eq]
      rw [hx]
    rw [← hpre, hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply_symm hT]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hih] with s hs
    have hpoly : Polynomial.map (MvPolynomial.eval s) g ≠ 0 := by
      intro h0
      apply hs
      have := congrArg (fun q => Polynomial.coeff q g.natDegree) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
      exact this
    have hfin : ((fun y => (y, s)) ⁻¹' T).Finite := by
      refine (Polynomial.roots
        (Polynomial.map (MvPolynomial.eval s) g)).toFinset.finite_toSet.subset ?_
      intro y hy
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, T, MvPolynomial.eval_eq_eval_mv_eval']
        at hy
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hpoly,
        Polynomial.IsRoot.def]
      exact hy
    simpa using hfin.measure_zero μ

/-- **Zero sets of polynomials are null.** The zero set of a nonzero polynomial in
finitely many variables is null for a product of copies of an atomless sigma-finite measure on
`𝕜`.

Helper for HMT 2011 Prop A.5; atlas `gaussian-full-rank-ae`. -/
theorem ae_eval_ne_zero_normedField {ι : Type*} [Fintype ι] (μ : Measure 𝕜)
    [SigmaFinite μ] [NullSingletonClass μ] (f : MvPolynomial ι 𝕜) (hf : f ≠ 0) :
    ∀ᵐ x ∂(Measure.pi fun _ : ι => μ), MvPolynomial.eval x f ≠ 0 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hg : MvPolynomial.rename e f ≠ 0 := by
    intro h; apply hf
    exact MvPolynomial.rename_injective e e.injective (by rw [h, map_zero])
  have h := ae_eval_ne_zero_normedField_fin μ _ _ hg
  let T : (Fin (Fintype.card ι) → 𝕜) → (ι → 𝕜) := fun y i => y (e i)
  have hT : Measurable T := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hmap : Measure.map T (Measure.pi fun _ => μ) = Measure.pi fun _ : ι => μ := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hT (MeasurableSet.univ_pi hs)]
    have hpre : T ⁻¹' Set.univ.pi s = Set.univ.pi fun k => s (e.symm k) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_univ_pi, T]
      constructor
      · intro hy k; simpa using hy (e.symm k)
      · intro hy i; simpa using hy (e i)
    rw [hpre, Measure.pi_pi]
    exact Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
  have hmeas : MeasurableSet {x : ι → 𝕜 | MvPolynomial.eval x f ≠ 0} :=
    ((MvPolynomial.continuous_eval f).measurable (measurableSet_singleton 0)).compl
  rw [← hmap, ae_map_iff hT.aemeasurable hmeas]
  filter_upwards [h] with y hy
  rw [MvPolynomial.eval_rename] at hy
  exact hy


end MvPolynomial
