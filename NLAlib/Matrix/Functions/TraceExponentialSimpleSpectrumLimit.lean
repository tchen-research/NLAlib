import NLAlib.Matrix.Functions.TraceExponentialMeasure
import NLAlib.Matrix.Functions.UnitaryCalculus
import NLAlib.ForMathlib.Analysis.SpecificLimits.StrictAntiApproximation

/-!
# Reduction from simple diagonal pencils to arbitrary Hermitian pencils

Strictly decreasing convex perturbations of the ordered spectrum stay in the
original spectral interval. Compactness of finite positive measures then removes
the simple-spectrum assumption. Scalar directions and empty matrices use the
already proved commuting case. This is the approximation reduction in Stahl's
positive-measure representation theorem.
-/

noncomputable section

open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive-measure representation for every simple real diagonal direction
implies the representation for arbitrary Hermitian directions. The approximation
stays in the limiting direction's exact spectral interval; repeated eigenvalues,
scalar directions, and empty dimension are all included. The simple diagonal
case is the explicit remaining premise of this reduction theorem.

atlas: trace-exponential-stahl (partial) -/
theorem exists_isCompactExpRepresentation_traceExp_of_diagonal_simple
    (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hsimple : ∀ (C : Matrix n n ℂ), C.IsHermitian →
      ∀ (b : n → ℝ), Function.Injective b → ∀ l u : ℝ, l ≤ u →
        (∀ i, b i ∈ Icc l u) → ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
          (fun t : ℝ => traceExp (C + t • diagonal (fun i => (b i : ℂ)))) l u) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => traceExp (A + t • H)) (lambdaMin H) (lambdaMax H) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have := hn
    exact exists_isCompactExpRepresentation_traceExp_of_commute A H hA hH
      (Subsingleton.elim _ _)
  | inr hn =>
    have := hn
    let l := lambdaMin H
    let u := lambdaMax H
    have hfin : (spectrum ℝ H).Finite := by
      rw [hH.spectrum_real_eq_range_eigenvalues]
      exact finite_range _
    have hbmem (i : n) : hH.eigenvalues i ∈ Icc l u := by
      have hi := hH.eigenvalues_mem_spectrum_real i
      exact ⟨csInf_le hfin.bddBelow hi, le_csSup hfin.bddAbove hi⟩
    let E := Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) (star hH.eigenvectorUnitary)
    have hEH : E H = diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
      simpa only [E, Function.comp_def, RCLike.ofReal_eq_complex_ofReal,
        Unitary.conjStarAlgAut_apply] using
        hH.conjStarAlgAut_star_eigenvectorUnitary
    have hlu : l ≤ u := by
      obtain ⟨i⟩ := hn
      exact (hbmem i).1.trans (hbmem i).2
    by_cases hsame : l = u
    · have hscalar : H = (l : ℝ) • (1 : Matrix n n ℂ) := by
        apply E.injective
        change E H = E ((l : ℝ) • (1 : Matrix n n ℂ))
        rw [hEH, map_smul, map_one]
        have heig (i : n) : hH.eigenvalues i = l := by
          have hi := hbmem i
          rw [← hsame] at hi
          exact le_antisymm hi.2 hi.1
        ext i j
        by_cases hij : i = j <;> simp [hij, heig, Complex.real_smul]
      apply exists_isCompactExpRepresentation_traceExp_of_commute A H hA hH
      rw [hscalar]
      exact (Commute.one_right A).smul_right l
    have hlt : l < u := lt_of_le_of_ne hlu hsame
    let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
    have hb0mem (i : Fin (Fintype.card n)) : hH.eigenvalues₀ i ∈ Icc l u := by
      simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using hbmem (e i)
    obtain ⟨v, hvstrict, hvmem, hvlim⟩ :=
      Fin.exists_strictAnti_tendsto_mem_Icc hH.eigenvalues₀_antitone hlt hb0mem
    let b : ℕ → n → ℝ := fun k i => v k (e.symm i)
    have hbinj (k : ℕ) : Function.Injective (b k) :=
      (hvstrict k).injective.comp e.symm.injective
    have hbinterval (k : ℕ) (i : n) : b k i ∈ Icc l u := hvmem k (e.symm i)
    have hblim : Tendsto b atTop (𝓝 hH.eigenvalues) := by
      apply tendsto_pi_nhds.mpr
      intro i
      exact (tendsto_pi_nhds.mp hvlim) (e.symm i)
    let K : ℕ → Matrix n n ℂ := fun k => diagonal (fun i => (b k i : ℂ))
    have hKlim : Tendsto K atTop (𝓝 (E H)) := by
      rw [hEH]
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_pi_nhds.mpr
      intro j
      by_cases hij : i = j
      · subst j
        simpa only [K, diagonal_apply_eq, Function.comp_def] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hblim) i)
      · simpa only [K, diagonal_apply_ne _ hij] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    have hEA : (E A).IsHermitian :=
      isHermitian_unitary_conj (star hH.eigenvectorUnitary) A hA
    obtain ⟨ν, hν⟩ := exists_isCompactExpRepresentation_traceExp_of_tendsto
      (fun _ : ℕ => E A) K (E A) (E H) l u tendsto_const_nhds hKlim
      (Eventually.of_forall fun k => hsimple (E A) hEA (b k) (hbinj k) l u hlu (hbinterval k))
    refine ⟨ν, ?_⟩
    convert hν using 1
    funext t
    rw [← map_smul E, ← map_add E]
    exact (traceExp_unitary_conj (star hH.eigenvectorUnitary) (A + t • H)).symm

end NLAlib
