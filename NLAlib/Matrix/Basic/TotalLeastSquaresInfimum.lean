import NLAlib.Matrix.Basic.TotalLeastSquares
import Mathlib.Topology.Order.OrderClosed
/-!+# The sharp TLS infimum, including unattained problems

The finite-solution chart is dense in the unit sphere. Perturbing a minimum
eigenvector in its last coordinate and normalizing gives actual feasible
corrections whose costs converge to the full-domain smallest Gram eigenvalue.
No attainment or spectral gap is assumed.
-/
noncomputable section
open Matrix Filter Topology
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Normalization is continuous at every nonzero coordinate vector. -/
theorem continuousAt_unitNormalize {ι : Type*} [Fintype ι] (v : ι → 𝕜) (hv : v ≠ 0) :
    ContinuousAt (unitNormalize : (ι → 𝕜) → (ι → 𝕜)) v := by
  have hn : (‖WithLp.toLp 2 v‖ : 𝕜) ≠ 0 := by
    have hh : ‖WithLp.toLp 2 v‖ ≠ 0 := by
      intro hz; exact hv (congrArg WithLp.ofLp (norm_eq_zero.mp hz))
    exact_mod_cast hh
  apply continuousAt_pi.mpr
  intro i
  change ContinuousAt (fun w : ι → 𝕜 => (‖WithLp.toLp 2 w‖ : 𝕜)⁻¹ * w i) v
  apply ContinuousAt.mul
  · apply ContinuousAt.inv₀
    · fun_prop
    · exact hn
  · exact (continuous_apply i).continuousAt

/-- All costs of actual finite total-least-squares corrections. -/
def tlsCorrectionCosts (A : Matrix m n 𝕜) (b : m → 𝕜) : Set ℝ :=
  {a | ∃ x D, IsTLSFeasible A b x D ∧ frobSq D = a}

/-- The full augmented-domain smallest Gram eigenvalue is the greatest
lower bound of actual finite TLS costs. This includes cases in which the
infimum is not attained.
atlas: total-least-squares-svd (partial) -/
theorem isGLB_tlsCorrectionCosts (A : Matrix m n 𝕜) (b : m → 𝕜) :
    IsGLB (tlsCorrectionCosts A b) (tlsValue A b) := by
  constructor
  · rintro a ⟨x, D, hD, rfl⟩
    exact tlsValue_le_frobSq_of_feasible A b x D hD
  · intro a ha
    let C := tlsDataMatrix A b
    obtain ⟨v, hv, he⟩ := (Matrix.isHermitian_conjTranspose_mul_self C).exists_unit_lambdaMin_eigenvector
    have hvalue : ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 = tlsValue A b :=
      (norm_mulVec_sq_eq_lambdaMin_gram_iff C hv).mpr he
    by_cases hlast : v (Sum.inr ()) ≠ 0
    · have hc : frobSq (rankOneCancel C v) ∈ tlsCorrectionCosts A b :=
        ⟨tlsSolutionOfVector v, rankOneCancel C v, isTLSFeasible_rankOneCancel A b v hv hlast, rfl⟩
      simpa only [frobSq_rankOneCancel C v hv, hvalue] using ha hc
    · have hvlast : v (Sum.inr ()) = 0 := not_ne_iff.mp hlast
      let w : ℝ → (n ⊕ Unit → 𝕜) :=
        fun t => v + (t : 𝕜) • Pi.single (Sum.inr ()) 1
      have hwlast (t : ℝ) : w t (Sum.inr ()) = (t : 𝕜) := by
        simp [w, hvlast, smul_eq_mul, RCLike.real_smul_eq_coe_mul]
      have hv0 : v ≠ 0 := by intro hh; simp [hh] at hv
      have hw : Tendsto w (𝓝[>] (0 : ℝ)) (𝓝 v) := by
        have hc : ContinuousAt w 0 := by dsimp only [w]; fun_prop
        simpa [w] using! hc.tendsto.mono_left inf_le_left
      have hn : Tendsto (fun t => unitNormalize (w t)) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
        have hh := (continuousAt_unitNormalize v hv0).tendsto.comp hw
        simpa only [unitNormalize, hv, RCLike.ofReal_one, inv_one, one_smul,
          Function.comp_def] using! hh
      have hcost : Tendsto (fun t => ‖WithLp.toLp 2 (C *ᵥ unitNormalize (w t))‖ ^ 2)
          (𝓝[>] (0 : ℝ)) (𝓝 (tlsValue A b)) := by
        have hc : Continuous (fun u : n ⊕ Unit → 𝕜 => ‖WithLp.toLp 2 (C *ᵥ u)‖ ^ 2) := by
          fun_prop
        simpa only [hvalue, Function.comp_def] using! hc.continuousAt.tendsto.comp hn
      apply ge_of_tendsto hcost
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hlast : w t (Sum.inr ()) ≠ 0 := by
        rw [hwlast]
        exact_mod_cast ne_of_gt ht
      have hwt : w t ≠ 0 := fun hh => hlast (congrFun hh (Sum.inr ()))
      have hunit := norm_unitNormalize (w t) hwt
      have hnormlast := unitNormalize_apply_ne_zero (w t) (Sum.inr ()) hlast
      have hc : frobSq (rankOneCancel C (unitNormalize (w t))) ∈ tlsCorrectionCosts A b :=
        ⟨tlsSolutionOfVector (unitNormalize (w t)), rankOneCancel C (unitNormalize (w t)),
          isTLSFeasible_rankOneCancel A b _ hunit hnormlast, rfl⟩
      simpa only [frobSq_rankOneCancel C _ hunit] using ha hc

end NLAlib
