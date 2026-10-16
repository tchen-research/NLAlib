import NLAlib.Matrix.Basic.GeneralTikhonovFilter
import NLAlib.Matrix.Basic.ResidualEnergy
import NLAlib.ForMathlib.Analysis.PenaltyLimits
/-!+# Variational meanings of the two general Tikhonov endpoints

The vanishing-parameter limit is the least-penalty least-squares solution.
The diverging-parameter limit is the least-squares solution constrained to
the penalty kernel. Triviality of the common kernel makes both unique.

Source: Hansen, §4.4; matrix-toolkit re-derivation §28.
Atlas: `general-form-tikhonov-gsvd`.
-/
noncomputable section
open Matrix Filter Topology
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

/-- Least data error, followed by least penalty among all best data fits. -/
def IsMinimumPenaltyLeastSquares (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) (x : n → 𝕜) : Prop :=
  (∀ z, residualEnergy A b x ≤ residualEnergy A b z) ∧
    ∀ z, (∀ y, residualEnergy A b z ≤ residualEnergy A b y) →
      residualEnergy L 0 x ≤ residualEnergy L 0 z

/-- A best data fit subject to lying in the entire penalty kernel. -/
def IsPenaltyKernelLeastSquares (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) (x : n → 𝕜) : Prop :=
  L *ᵥ x = 0 ∧ ∀ z, L *ᵥ z = 0 → residualEnergy A b x ≤ residualEnergy A b z

/-- The zero-parameter GSVD endpoint has exactly the least-penalty
least-squares interpretation; it is not generally the data pseudoinverse.
atlas: general-form-tikhonov-gsvd (partial) -/
theorem IsNormalizedGSVD.zeroLimit_minimumPenaltyLeastSquares
    {A : Matrix m n 𝕜} {L : Matrix p n 𝕜} {X : Matrix n n 𝕜} {c s : n → ℝ}
    (h : IsNormalizedGSVD A L X c s) (b : m → 𝕜) :
    IsMinimumPenaltyLeastSquares A L b (generalTikhonovZeroLimit A X c b) := by
  let f : EuclideanSpace 𝕜 n → ℝ := fun x => residualEnergy A b x.ofLp
  let g : EuclideanSpace 𝕜 n → ℝ := fun x => residualEnergy L 0 x.ofLp
  have hf : Continuous f := by dsimp [f, residualEnergy]; fun_prop
  have hg : Continuous g := by dsimp [g, residualEnergy]; fun_prop
  have hh := vanishing_penalty_limit_minimizes hf hg
    (fun β => (WithLp.toLp 2 (generalTikhonovFilter A X c s b β) : EuclideanSpace 𝕜 n))
    (WithLp.toLp 2 (generalTikhonovZeroLimit A X c b))
    (h.tendsto_generalTikhonovFilter_zero b) (by
      intro β hβ z
      simpa [f, g, residualEnergy, generalTikhonovObjective] using
        h.generalTikhonovFilter_minimizer b hβ z.ofLp)
  constructor
  · intro z
    exact hh.1 (WithLp.toLp 2 z)
  · intro z hz
    apply hh.2 (WithLp.toLp 2 z)
    intro y
    exact hz y.ofLp

/-- The infinite-parameter GSVD endpoint is a least-squares solution
on the penalty kernel.
atlas: general-form-tikhonov-gsvd (partial) -/
theorem IsNormalizedGSVD.infinityLimit_penaltyKernelLeastSquares
    {A : Matrix m n 𝕜} {L : Matrix p n 𝕜} {X : Matrix n n 𝕜} {c s : n → ℝ}
    (h : IsNormalizedGSVD A L X c s) (b : m → 𝕜) :
    IsPenaltyKernelLeastSquares A L b (generalTikhonovInfinityLimit A X c s b) := by
  let f : EuclideanSpace 𝕜 n → ℝ := fun x => residualEnergy A b x.ofLp
  let g : EuclideanSpace 𝕜 n → ℝ := fun x => residualEnergy L 0 x.ofLp
  have hf : Continuous f := by dsimp [f, residualEnergy]; fun_prop
  have hg : Continuous g := by dsimp [g, residualEnergy]; fun_prop
  have hh := diverging_penalty_limit_minimizes hf hg
    (fun x => sq_nonneg _) (fun x => sq_nonneg _)
    (fun β => (WithLp.toLp 2 (generalTikhonovFilter A X c s b β) : EuclideanSpace 𝕜 n))
    (WithLp.toLp 2 (generalTikhonovInfinityLimit A X c s b))
    (h.tendsto_generalTikhonovFilter_infinity b) 0 (by simp [g, residualEnergy]) (by
      intro β hβ z
      simpa [f, g, residualEnergy, generalTikhonovObjective] using
        h.generalTikhonovFilter_minimizer b hβ z.ofLp)
  constructor
  · have hn : ‖WithLp.toLp 2 (L *ᵥ generalTikhonovInfinityLimit A X c s b)‖ = 0 := by
      simpa [g, residualEnergy] using (sq_eq_zero_iff.mp hh.1)
    exact congrArg WithLp.ofLp (norm_eq_zero.mp hn)
  · intro z hz
    apply hh.2 (WithLp.toLp 2 z)
    simp [g, residualEnergy, hz]

/-- The least-penalty least-squares solution is unique exactly in the
directions where the data and penalty kernels have trivial intersection. -/
theorem IsMinimumPenaltyLeastSquares.unique {A : Matrix m n 𝕜} {L : Matrix p n 𝕜}
    {b : m → 𝕜} {x y : n → 𝕜} (hx : IsMinimumPenaltyLeastSquares A L b x)
    (hy : IsMinimumPenaltyLeastSquares A L b y)
    (hN : ∀ v : n → 𝕜, A *ᵥ v = 0 → L *ᵥ v = 0 → v = 0) : x = y := by
  have hA := mulVec_eq_of_residualEnergy_minimizers A b x y hx.1 (hy.1 x)
  let z := (1 / 2 : 𝕜) • (x + y)
  have hf : residualEnergy A b y = residualEnergy A b x := le_antisymm (hy.1 x) (hx.1 y)
  have hm : residualEnergy A b z = residualEnergy A b x := by
    have he := residualEnergy_midpoint A b x y
    rw [hA] at he
    simp only [WithLp.toLp_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at he
    dsimp only [z]
    linarith
  have hz : ∀ w, residualEnergy A b z ≤ residualEnergy A b w := by
    intro w; rw [hm]; exact hx.1 w
  have hpen := hx.2 z hz
  have hpen' := hy.2 x hx.1
  have he := residualEnergy_midpoint L 0 x y
  have hn : ‖WithLp.toLp 2 (L *ᵥ (x - y))‖ = 0 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 (L *ᵥ (x - y)))]
  exact sub_eq_zero.mp (hN (x - y) hA (congrArg WithLp.ofLp (norm_eq_zero.mp hn)))

/-- The constrained endpoint is unique under the same common-kernel
condition, whether or not either matrix individually has full rank. -/
theorem IsPenaltyKernelLeastSquares.unique {A : Matrix m n 𝕜} {L : Matrix p n 𝕜}
    {b : m → 𝕜} {x y : n → 𝕜} (hx : IsPenaltyKernelLeastSquares A L b x)
    (hy : IsPenaltyKernelLeastSquares A L b y)
    (hN : ∀ v : n → 𝕜, A *ᵥ v = 0 → L *ᵥ v = 0 → v = 0) : x = y := by
  have hL : L *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hx.1, hy.1, sub_self]
  have hmid : L *ᵥ ((1 / 2 : 𝕜) • (x + y)) = 0 := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, hx.1, hy.1, add_zero, smul_zero]
  have hm := hx.2 _ hmid
  have hyx := hy.2 x hx.1
  have he := residualEnergy_midpoint A b x y
  have hn : ‖WithLp.toLp 2 (A *ᵥ (x - y))‖ = 0 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 (A *ᵥ (x - y)))]
  exact sub_eq_zero.mp (hN (x - y) (congrArg WithLp.ofLp (norm_eq_zero.mp hn)) hL)

/-- Both parameter limits have their unique intended variational meaning
whenever the common kernel is trivial.
atlas: general-form-tikhonov-gsvd (partial) -/
theorem IsNormalizedGSVD.generalTikhonov_endpoints_unique
    {A : Matrix m n 𝕜} {L : Matrix p n 𝕜} {X : Matrix n n 𝕜} {c s : n → ℝ}
    (h : IsNormalizedGSVD A L X c s)
    (hN : ∀ v : n → 𝕜, A *ᵥ v = 0 → L *ᵥ v = 0 → v = 0) (b : m → 𝕜) :
    (IsMinimumPenaltyLeastSquares A L b (generalTikhonovZeroLimit A X c b) ∧
      ∀ z, IsMinimumPenaltyLeastSquares A L b z → z = generalTikhonovZeroLimit A X c b) ∧
    (IsPenaltyKernelLeastSquares A L b (generalTikhonovInfinityLimit A X c s b) ∧
      ∀ z, IsPenaltyKernelLeastSquares A L b z → z = generalTikhonovInfinityLimit A X c s b) := by
  have hz := h.zeroLimit_minimumPenaltyLeastSquares b
  have hi := h.infinityLimit_penaltyKernelLeastSquares b
  exact ⟨⟨hz, fun z hzz => hzz.unique hz hN⟩, ⟨hi, fun z hzz => hzz.unique hi hN⟩⟩

end NLAlib
