import NLAlib.Estimation.Reconstruction.NormalSpectralScaledQuadrature

/-!
# Scalar work and retained arrays of normal spectral reconstruction

The actual recurrence histories were counted in `normalMixedProgramScalarWork`.
This adds the one multiplication for each normalized oracle-response coordinate
and the finite density coefficient readout. Fixed coefficients are available
before the oracle is supplied. The finite quadrature's two separable transforms
have their independently checked cubic scalar budget.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n]

/-- One scalar multiplication removes the supplied physical scale. -/
def normalResponseScalarProgram (S : ℝ) (x : ℂ) : ScalarProgram ℂ :=
  .mul (.input (S⁻¹ : ℂ)) (.input x)

/-- The counted response is exactly the response adapter in the native strategy. -/
theorem run_normalResponseScalarProgram (S : ℝ) (x : ℂ) :
    (normalResponseScalarProgram S x).run = S⁻¹•x := by
  simp [normalResponseScalarProgram, ScalarProgram.run, RCLike.real_smul_eq_coe_mul]

/-- Each actual primitive response coordinate costs one multiplication. -/
theorem cost_normalResponseScalarProgram (S : ℝ) (x : ℂ) :
    (normalResponseScalarProgram S x).cost = 1 := rfl

/-- One density coefficient read from the observed table. -/
def normalDensityCoefficientScalarProgram (M : ℕ)
    (Γ : Matrix (Fin (M+1)) (Fin (M+1)) ℂ) (α : Fin 2 → ℕ) : ScalarProgram ℝ :=
  .mul (.input (tensorChebyshevJacksonDamping M α)) (.input (normalMomentTable M Γ α))

/-- These literal coefficients evaluate to the actual density postprocessor. -/
theorem normalMomentDensity_eq_sum_scalar_coefficients (M : ℕ)
    (Γ : Matrix (Fin (M+1)) (Fin (M+1)) ℂ) (x : Fin 2 → ℝ) :
    normalMomentDensity M Γ x =
      ∑ α ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (M+1)),
        (normalDensityCoefficientScalarProgram M Γ α).run*tensorNormalizedChebyshev α x := by
  apply Finset.sum_congr rfl
  intro α _
  dsimp [normalDensityCoefficientScalarProgram, ScalarProgram.run]
  ring

/-- All retained density coefficient readouts together cost `(M+1)^2`. -/
theorem sum_cost_normalDensityCoefficientScalarProgram (M : ℕ)
    (Γ : Matrix (Fin (M+1)) (Fin (M+1)) ℂ) :
    (∑ α ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (M+1)),
      (normalDensityCoefficientScalarProgram M Γ α).cost) = (M+1)^2 := by
  simp [normalDensityCoefficientScalarProgram, ScalarProgram.cost, Fintype.card_piFinset, pow_two]

/-- Cost of normalizing every actual response in the two recurrence histories:
two components, `M` degrees, two primitive products and every vector coordinate. -/
def normalScaledResponseScalarWork (S : ℝ) (b : n → ℂ) (M : ℕ)
    (oracle : Bool × (n → ℂ) → n → ℂ) : ℕ :=
  let f := (fun v : n → ℂ => S⁻¹•v) ∘ oracle
  ∑ imaginary : Bool, ∑ k : Fin M, ∑ adjoint : Bool, ∑ r : n,
    (normalResponseScalarProgram S
      (oracle (adjoint,((hermitianPartChebyshevProgram imaginary b k.val).run f) k.val) r)).cost

/-- The adapter performs one scalar multiplication for every primitive
response coordinate, on the actual native recurrence histories. -/
theorem normalScaledResponseScalarWork_eq (S : ℝ) (b : n → ℂ) (M : ℕ)
    (oracle : Bool × (n → ℂ) → n → ℂ) :
    normalScaledResponseScalarWork S b M oracle = 4*Fintype.card n*M := by
  simp [normalScaledResponseScalarWork, cost_normalResponseScalarProgram]
  ring

/-- The actual recurrence history plus physical response normalization and all
finite density coefficient readouts. -/
def normalScaledSpectralDensityScalarWork (S : ℝ) (b : n → ℂ) (M : ℕ)
    (oracle : Bool × (n → ℂ) → n → ℂ) : ℕ :=
  let f := (fun v : n → ℂ => S⁻¹•v) ∘ oracle
  let Γ := (normalMixedMomentProgram b M).run f
  normalMixedProgramScalarWork b M f + normalScaledResponseScalarWork S b M oracle +
    ∑ α ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (M+1)),
      (normalDensityCoefficientScalarProgram M Γ α).cost

/-- The actual supplied-scale strategy has linear dimension and quadratic
degree scalar work, with an explicit uniform constant.
atlas: normal-spectral-density-query (partial) -/
theorem normalScaledSpectralDensityScalarWork_le [Nonempty n] (S : ℝ) (b : n → ℂ) (M : ℕ)
    (oracle : Bool × (n → ℂ) → n → ℂ) :
    normalScaledSpectralDensityScalarWork S b M oracle ≤ 18*Fintype.card n*(M+1)^2 := by
  unfold normalScaledSpectralDensityScalarWork
  dsimp only
  rw [sum_cost_normalDensityCoefficientScalarProgram, normalScaledResponseScalarWork_eq]
  have hh := normalMixedProgramScalarWork_le b M ((fun v : n → ℂ => S⁻¹•v) ∘ oracle)
  have hm : M ≤ (M+1)^2 := by nlinarith
  have hg := Nat.mul_le_mul_left (4*Fintype.card n) hm
  have hn : 1 ≤ Fintype.card n := Fintype.card_pos
  have hr := Nat.mul_le_mul_right ((M+1)^2) hn
  nlinarith

/-- In the card's positive-degree range this is explicitly at most `72nM^2`. -/
theorem normalScaledSpectralDensityScalarWork_le_sq [Nonempty n] (S : ℝ) (b : n → ℂ)
    {M : ℕ} (hM : 1 ≤ M) (oracle : Bool × (n → ℂ) → n → ℂ) :
    normalScaledSpectralDensityScalarWork S b M oracle ≤ 72*Fintype.card n*M^2 := by
  have hh := normalScaledSpectralDensityScalarWork_le S b M oracle
  have hm := Nat.mul_le_mul_left M hM
  have hs : (M+1)^2 ≤ 4*M^2 := by nlinarith
  have hg := Nat.mul_le_mul_left (18*Fintype.card n) hs
  nlinarith

/-- Two retained vector tables, the full moment array, and four working vectors. -/
abbrev NormalMixedStorageIndex (n : Type*) (M : ℕ) :=
  (Fin 2 × n × Fin (M+1)) ⊕ (Fin (M+1) × Fin (M+1)) ⊕ (Fin 4 × n)

/-- The finite native dataflow stores the two vector arrays, every moment and
four vector buffers, with this exact scalar-slot count. -/
theorem card_normalMixedStorageIndex (M : ℕ) :
    Fintype.card (NormalMixedStorageIndex n M) =
      2*Fintype.card n*(M+1)+(M+1)^2+4*Fintype.card n := by
  simp [NormalMixedStorageIndex, Fintype.card_prod, Fintype.card_sum]
  ring

/-- The explicit retained-array budget has the source's `O(nM+M^2)` size.
atlas: normal-spectral-density-query (partial) -/
theorem card_normalMixedStorageIndex_le {M : ℕ} (hM : 1 ≤ M) :
    Fintype.card (NormalMixedStorageIndex n M) ≤ 8*Fintype.card n*M+4*M^2 := by
  rw [card_normalMixedStorageIndex]
  have hn := Nat.mul_le_mul_left (Fintype.card n) hM
  have hm := Nat.mul_le_mul_left M hM
  nlinarith

end NLAlib
