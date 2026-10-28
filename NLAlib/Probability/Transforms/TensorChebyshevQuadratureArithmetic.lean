import NLAlib.Probability.Transforms.TensorChebyshevQuadrature
import NLAlib.Krylov.QueryModel.ScalarArithmetic

/-!
# Separable cubic scalar work for the positive tensor quadrature

Two dense evaluation transforms compute every sampled density. Fixed nodes,
basis evaluations and damping coefficients are available before oracle queries.
The counted scalar programs include damping, both transforms and final weights.
-/

noncomputable section
open Real Matrix MeasureTheory Finset
namespace NLAlib

/-- Precomputed normalized polynomial values at the actual Gauss root grid. -/
def tensorChebyshevGaussBasis (M : ℕ) : Matrix (Fin (M+1)) (Fin (M+1)) ℝ :=
  fun grid mode => normalizedChebyshev mode (chebyshevZero (M+1) grid)

/-- The literal two-multiplication damping of one supplied mixed moment. -/
def tensorChebyshevDampingScalarProgram (M : ℕ) (j k : Fin (M+1)) (m : ℝ) : ScalarProgram ℝ :=
  .mul (.mul (.input (chebyshevJacksonDamping M j))
    (.input (chebyshevJacksonDamping M k))) (.input m)

/-- Every damped coefficient uses two actual scalar multiplications. -/
theorem cost_tensorChebyshevDampingScalarProgram (M : ℕ) (j k : Fin (M+1)) (m : ℝ) :
    (tensorChebyshevDampingScalarProgram M j k m).cost = 2 := rfl

/-- The coefficient program evaluates to the native product Jackson damping. -/
theorem run_tensorChebyshevDampingScalarProgram (M : ℕ) (j k : Fin (M+1)) (m : ℝ) :
    (tensorChebyshevDampingScalarProgram M j k m).run =
      chebyshevJacksonDamping M j*chebyshevJacksonDamping M k*m := rfl

/-- The full damped coefficient matrix, using the supplied actual moments. -/
def tensorChebyshevDampedMoments (M : ℕ) (m : Matrix (Fin (M+1)) (Fin (M+1)) ℝ) :
    Matrix (Fin (M+1)) (Fin (M+1)) ℝ :=
  fun j k => (tensorChebyshevDampingScalarProgram M j k (m j k)).run

/-- A literal scalar entry of a dense separable evaluation transform. -/
def tensorChebyshevTransformScalarProgram {L : ℕ} (X Y : Matrix (Fin L) (Fin L) ℝ)
    (j k : Fin L) : ScalarProgram ℝ :=
  innerProductScalarProgram (fun r => X j r) (fun r => Y r k)

/-- The transform entry program computes the actual dense matrix product. -/
theorem run_tensorChebyshevTransformScalarProgram {L : ℕ} (X Y : Matrix (Fin L) (Fin L) ℝ)
    (j k : Fin L) : (tensorChebyshevTransformScalarProgram X Y j k).run = (X*Y) j k := by
  rw [tensorChebyshevTransformScalarProgram,run_innerProductScalarProgram]
  simp [dotProduct,Matrix.mul_apply]

/-- Three charged scalar operations per inner coordinate suffice for each entry. -/
theorem cost_tensorChebyshevTransformScalarProgram {L : ℕ} (X Y : Matrix (Fin L) (Fin L) ℝ)
    (j k : Fin L) : (tensorChebyshevTransformScalarProgram X Y j k).cost = 3*L :=
  cost_innerProductScalarProgram _ _

/-- The final sampled-density weight uses one multiplication by a fixed constant. -/
def tensorChebyshevWeightScalarProgram (M : ℕ) (x : ℝ) : ScalarProgram ℝ :=
  .mul (.input ((π/(M+1))^2)) (.input x)

/-- The grid weight normalization costs one scalar multiplication. -/
theorem cost_tensorChebyshevWeightScalarProgram (M : ℕ) (x : ℝ) :
    (tensorChebyshevWeightScalarProgram M x).cost = 1 := rfl

/-- Literal scalar work for all coefficient damping, both dense transforms and
every final weight; intermediate matrix products are reused entry by entry. -/
def tensorChebyshevQuadratureScalarWork (M : ℕ)
    (m : Matrix (Fin (M+1)) (Fin (M+1)) ℝ) : ℕ :=
  let B := tensorChebyshevGaussBasis M
  let D := tensorChebyshevDampedMoments M m
  (∑ j,∑ k,(tensorChebyshevDampingScalarProgram M j k (m j k)).cost) +
  (∑ j,∑ k,(tensorChebyshevTransformScalarProgram B D j k).cost) +
  (∑ j,∑ k,(tensorChebyshevTransformScalarProgram (B*D) Bᵀ j k).cost) +
  ∑ j,∑ k,(tensorChebyshevWeightScalarProgram M ((B*D*Bᵀ) j k)).cost

/-- The explicit two-transform procedure uses at most `9(M+1)^3` operations. -/
theorem tensorChebyshevQuadratureScalarWork_le (M : ℕ)
    (m : Matrix (Fin (M+1)) (Fin (M+1)) ℝ) :
    tensorChebyshevQuadratureScalarWork M m ≤ 9*(M+1)^3 := by
  simp only [tensorChebyshevQuadratureScalarWork,cost_tensorChebyshevDampingScalarProgram,
    cost_tensorChebyshevTransformScalarProgram,cost_tensorChebyshevWeightScalarProgram,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [Nat.cast_id]
  nlinarith [Nat.zero_le (3*M*(M+1)^2)]

private theorem sum_fin2_piFinset_eq_sum_fin (M : ℕ) (F : (Fin 2 → ℕ) → ℝ) :
    (∑ α ∈ Fintype.piFinset (fun _ : Fin 2 => range (M+1)),F α) =
      ∑ j : Fin (M+1),∑ k : Fin (M+1),F ![j.val,k.val] := by
  rw [← Fintype.sum_prod_type (fun p : Fin (M+1) × Fin (M+1) => F ![p.1.val,p.2.val])]
  apply Finset.sum_bij (fun α hα =>
    ((⟨α 0,mem_range.mp (Fintype.mem_piFinset.mp hα 0)⟩ : Fin (M+1)),
      (⟨α 1,mem_range.mp (Fintype.mem_piFinset.mp hα 1)⟩ : Fin (M+1))))
  · intro α _;exact mem_univ _
  · intro α hα β hβ hab
    funext i
    fin_cases i
    · exact congrArg (fun p : Fin (M+1) × Fin (M+1) => p.1.val) hab
    · exact congrArg (fun p : Fin (M+1) × Fin (M+1) => p.2.val) hab
  · intro p _
    refine ⟨![p.1.val,p.2.val],?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      fin_cases i
      · exact mem_range.mpr p.1.isLt
      · exact mem_range.mpr p.2.isLt
    · simp
  · intro α _
    congr 1
    ext i
    fin_cases i <;> simp

/-- Two actual dense evaluation transforms compute the positive density samples.
The supplied moments here are the native integrals of the input cube law. -/
theorem tensorChebyshevGaussBasis_mul_damped_eq_density
    (μ : Measure (chebyshevCube (Fin 2))) [IsProbabilityMeasure μ] (M : ℕ)
    (j k : Fin (M+1)) :
    (tensorChebyshevGaussBasis M * tensorChebyshevDampedMoments M
      (fun a b => tensorChebyshevMoment μ ![a.val,b.val]) * (tensorChebyshevGaussBasis M)ᵀ) j k =
      tensorChebyshevSmoothedDensity μ M
        (WithLp.ofLp (tensorGaussChebyshevNode (M+1) ![j,k])) := by
  rw [tensorChebyshevSmoothedDensity_eq_sum,sum_fin2_piFinset_eq_sum_fin]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,tensorChebyshevDampedMoments,
    run_tensorChebyshevDampingScalarProgram,tensorChebyshevGaussBasis,
    tensorChebyshevJacksonDamping,tensorNormalizedChebyshev,Fin.prod_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    tensorGaussChebyshevNode,WithLp.ofLp_toLp]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- All actual quadrature weights computed by the two separable dense transforms. -/
def tensorChebyshevQuadratureWeightMatrix (M : ℕ)
    (m : Matrix (Fin (M+1)) (Fin (M+1)) ℝ) : Matrix (Fin (M+1)) (Fin (M+1)) ℝ :=
  let B := tensorChebyshevGaussBasis M
  let D := tensorChebyshevDampedMoments M m
  fun j k => (tensorChebyshevWeightScalarProgram M ((B*D*Bᵀ) j k)).run

/-- The computed weights equal the positive native sampled-density weights. -/
theorem tensorChebyshevQuadratureWeightMatrix_eq_native
    (μ : Measure (chebyshevCube (Fin 2))) [IsProbabilityMeasure μ] (M : ℕ)
    (j k : Fin (M+1)) :
    tensorChebyshevQuadratureWeightMatrix M (fun a b => tensorChebyshevMoment μ ![a.val,b.val]) j k =
      (tensorChebyshevQuadratureWeight μ M ![j,k] : ℝ) := by
  dsimp only [tensorChebyshevQuadratureWeightMatrix,tensorChebyshevWeightScalarProgram,ScalarProgram.run]
  rw [tensorChebyshevGaussBasis_mul_damped_eq_density,
    coe_tensorChebyshevQuadratureWeight]
  simp

/-- Oracle-free finite-law readout from the supplied table of mixed moments. -/
def tensorChebyshevQuadratureLawOfMoments (M : ℕ)
    (m : Matrix (Fin (M+1)) (Fin (M+1)) ℝ) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  ∑ σ : Fin 2 → Fin (M+1),
    (tensorChebyshevQuadratureWeightMatrix M m (σ 0) (σ 1)).toNNReal •
      Measure.dirac (tensorGaussChebyshevNode (M+1) σ)

/-- The scalar-computable moment readout is exactly the actual positive
quadrature measure whenever the input moments are the native cube-law moments. -/
theorem tensorChebyshevQuadratureLawOfMoments_eq_native
    (μ : Measure (chebyshevCube (Fin 2))) [IsProbabilityMeasure μ] (M : ℕ) :
    tensorChebyshevQuadratureLawOfMoments M (fun a b => tensorChebyshevMoment μ ![a.val,b.val]) =
      tensorChebyshevQuadratureLaw μ M := by
  unfold tensorChebyshevQuadratureLawOfMoments tensorChebyshevQuadratureLaw
  apply Finset.sum_congr rfl
  intro σ _
  have he : ![σ 0,σ 1] = σ := by ext i;fin_cases i <;> rfl
  rw [tensorChebyshevQuadratureWeightMatrix_eq_native,he,Real.toNNReal_coe]

end NLAlib
