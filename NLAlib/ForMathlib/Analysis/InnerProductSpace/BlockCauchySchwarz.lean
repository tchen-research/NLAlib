/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false

/-!
# Block Cauchy--Schwarz for operator rows and columns

For families `a r : X →L[ℝ] Y` and `b r : Y →L[ℝ] Z` indexed by a finite type, the column
`blockAnalysis a : X →L[ℝ] PiLp 2 (fun _ ↦ Y)` and the row `blockSynthesis b` factor
`∑ r, b r ∘L a r`, which gives the operator Cauchy--Schwarz inequality
`‖∑ r, b r ∘L a r‖ ^ 2 ≤ ‖∑ r, (a r)† ∘L a r‖ * ‖∑ r, b r ∘L (b r)†‖`
(`norm_sum_comp_sq_le`) and its form with orthogonal projections
(`norm_sum_comp_sq_le_of_projections`). The middle space is the Hilbert direct sum (`PiLp 2`),
not a product with the supremum norm.

Used by the sparse-sketch trace-moment proof (the "typed block Cauchy--Schwarz" of the
manuscript, TeX lines 930--989).
-/

open scoped NNReal ENNReal InnerProduct
open WithLp

namespace NLAlib

noncomputable section

variable {R X Y Z : Type*}
variable [Fintype R]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The column operator `x ↦ (a r x)ₙ` into the Hilbert direct sum.

Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def blockAnalysisLinear (a : R → X →L[ℝ] Y) :
    X →ₗ[ℝ] PiLp 2 (fun _ : R ↦ Y) where
  toFun x := toLp 2 (fun r ↦ a r x)
  map_add' x y := by
    ext r
    simp
  map_smul' c x := by
    ext r
    simp

/-- The continuous column operator.  Continuity follows from finite
dimensionality of its domain.

Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def blockAnalysis (a : R → X →L[ℝ] Y) :
    X →L[ℝ] PiLp 2 (fun _ : R ↦ Y) :=
  ⟨blockAnalysisLinear a, (blockAnalysisLinear a).continuous_of_finiteDimensional⟩

omit [FiniteDimensional ℝ Y] in
/-- The analysis column evaluates to the chosen component operator.
Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp]
theorem blockAnalysis_apply (a : R → X →L[ℝ] Y) (x : X) (r : R) :
    blockAnalysis a x r = a r x :=
  rfl

/-- The row operator `(yₙ) ↦ ∑ r, b r (y r)` from the Hilbert direct sum.

Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def blockSynthesisLinear (b : R → Y →L[ℝ] Z) :
    PiLp 2 (fun _ : R ↦ Y) →ₗ[ℝ] Z where
  toFun y := ∑ r, b r (y r)
  map_add' x y := by
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    simp [Finset.smul_sum]

/-- The continuous row operator.

Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def blockSynthesis (b : R → Y →L[ℝ] Z) :
    PiLp 2 (fun _ : R ↦ Y) →L[ℝ] Z :=
  ⟨blockSynthesisLinear b,
    (blockSynthesisLinear b).continuous_of_finiteDimensional⟩

omit [FiniteDimensional ℝ Z] in
/-- The synthesis row evaluates to the sum of its component outputs.
Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp]
theorem blockSynthesis_apply (b : R → Y →L[ℝ] Z)
    (y : PiLp 2 (fun _ : R ↦ Y)) :
    blockSynthesis b y = ∑ r, b r (y r) :=
  rfl

omit [FiniteDimensional ℝ Z] in
/-- Composing the block row and column gives the sum of component compositions.
Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem blockSynthesis_comp_blockAnalysis_eq (a : R → X →L[ℝ] Y) (b : R → Y →L[ℝ] Z) :
    blockSynthesis b ∘L blockAnalysis a = ∑ r, b r ∘L a r := by
  ext x
  change (∑ r, b r (a r x)) = _
  simp

/-- The adjoint of a block analysis column is the row of component adjoints.
Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem blockAnalysis_adjoint (a : R → X →L[ℝ] Y) :
    (blockAnalysis a)† = blockSynthesis (fun r ↦ (a r)†) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (blockSynthesis (fun r ↦ (a r)†)) (blockAnalysis a)).2
  intro y x
  simp only [blockSynthesis_apply, blockAnalysis_apply, PiLp.inner_apply, sum_inner]
  apply Finset.sum_congr rfl
  intro r _
  exact ContinuousLinearMap.adjoint_inner_left (a r) x (y r)

/-- The adjoint of a block synthesis row is the column of component adjoints.
Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem blockSynthesis_adjoint (b : R → Y →L[ℝ] Z) :
    (blockSynthesis b)† = blockAnalysis (fun r ↦ (b r)†) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (blockAnalysis (fun r ↦ (b r)†)) (blockSynthesis b)).2
  intro z y
  simp only [blockAnalysis_apply, blockSynthesis_apply, PiLp.inner_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact ContinuousLinearMap.adjoint_inner_left (b r) (y r) z

/-- The block analysis Gram operator is the sum of component Gram operators.
Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem blockAnalysis_adjoint_comp_eq (a : R → X →L[ℝ] Y) :
    (blockAnalysis a)† ∘L blockAnalysis a = ∑ r, (a r)† ∘L a r := by
  rw [blockAnalysis_adjoint]
  exact blockSynthesis_comp_blockAnalysis_eq a (fun r ↦ (a r)†)

/-- The block synthesis co-Gram operator is the sum of component co-Gram operators.
Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem blockSynthesis_comp_adjoint_eq (b : R → Y →L[ℝ] Z) :
    blockSynthesis b ∘L (blockSynthesis b)† = ∑ r, b r ∘L (b r)† := by
  rw [blockSynthesis_adjoint]
  exact blockSynthesis_comp_blockAnalysis_eq (fun r ↦ (b r)†) b

/-- Typed block Cauchy--Schwarz without writing the projections explicitly:
the maps `a r` and `b r` may already contain the domain, middle, and range
projections.  This is the exact row/column-operator inequality.

Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_sum_comp_sq_le (a : R → X →L[ℝ] Y) (b : R → Y →L[ℝ] Z) :
    ‖∑ r, b r ∘L a r‖ ^ 2 ≤
      ‖∑ r, (a r)† ∘L a r‖ * ‖∑ r, b r ∘L (b r)†‖ := by
  let A := blockAnalysis a
  let B := blockSynthesis b
  have hcomp : B ∘L A = ∑ r, b r ∘L a r := blockSynthesis_comp_blockAnalysis_eq a b
  have hA : A† ∘L A = ∑ r, (a r)† ∘L a r := blockAnalysis_adjoint_comp_eq a
  have hB : B ∘L B† = ∑ r, b r ∘L (b r)† := blockSynthesis_comp_adjoint_eq b
  have hnorm : ‖B ∘L A‖ ≤ ‖B‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le B A
  calc
    ‖∑ r, b r ∘L a r‖ ^ 2 = ‖B ∘L A‖ ^ 2 := by rw [hcomp]
    _ ≤ (‖B‖ * ‖A‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (‖A‖ * ‖A‖) * (‖B‖ * ‖B‖) := by ring
    _ = ‖A† ∘L A‖ * ‖B ∘L B†‖ := by
      rw [ContinuousLinearMap.norm_adjoint_comp_self]
      have hBadj := ContinuousLinearMap.norm_adjoint_comp_self (B†)
      simp only [ContinuousLinearMap.adjoint_adjoint] at hBadj
      rw [hBadj, LinearIsometryEquiv.norm_map]
    _ = ‖∑ r, (a r)† ∘L a r‖ * ‖∑ r, b r ∘L (b r)†‖ := by rw [hA, hB]

/-- The displayed projection form of TeX equation (typed-block-CS).  The six
hypotheses say exactly that `E`, `F`, and `G` are orthogonal projections:
self-adjoint idempotents on their respective Hilbert spaces.

Source: ported from `SparseFockFormal.TypedBlockCS`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_sum_comp_sq_le_of_projections
    (E : X →L[ℝ] X) (F : Y →L[ℝ] Y) (G : Z →L[ℝ] Z)
    (hEadj : E† = E) (hFadj : F† = F) (hGadj : G† = G)
    (_hEid : E ∘L E = E) (hFid : F ∘L F = F) (_hGid : G ∘L G = G)
    (a : R → X →L[ℝ] Y) (b : R → Y →L[ℝ] Z) :
    ‖G ∘L (∑ r, (b r ∘L F) ∘L a r) ∘L E‖ ^ 2 ≤
      ‖E ∘L (∑ r, ((a r)† ∘L F) ∘L a r) ∘L E‖ *
      ‖G ∘L (∑ r, (b r ∘L F) ∘L (b r)†) ∘L G‖ := by
  let ap : R → X →L[ℝ] Y := fun r ↦ (F ∘L a r) ∘L E
  let bp : R → Y →L[ℝ] Z := fun r ↦ (G ∘L b r) ∘L F
  have hmain := norm_sum_comp_sq_le ap bp
  have hleft :
      ∑ r, bp r ∘L ap r = G ∘L (∑ r, (b r ∘L F) ∘L a r) ∘L E := by
    ext x
    simp only [ap, bp, sum_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, map_sum]
    apply Finset.sum_congr rfl
    intro r _
    congr 2
    change (F ∘L F) (a r (E x)) = F (a r (E x))
    rw [hFid]
  have hrightA :
      ∑ r, (ap r)† ∘L ap r =
        E ∘L (∑ r, ((a r)† ∘L F) ∘L a r) ∘L E := by
    ext x
    simp only [ap, ContinuousLinearMap.adjoint_comp, hEadj, hFadj,
      sum_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, map_sum]
    apply Finset.sum_congr rfl
    intro r _
    congr 2
    change (F ∘L F) (a r (E x)) = F (a r (E x))
    rw [hFid]
  have hrightB :
      ∑ r, bp r ∘L (bp r)† =
        G ∘L (∑ r, (b r ∘L F) ∘L (b r)†) ∘L G := by
    ext z
    simp only [bp, ContinuousLinearMap.adjoint_comp, hGadj, hFadj,
      sum_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, map_sum]
    apply Finset.sum_congr rfl
    intro r _
    congr 2
    change (F ∘L F) (((b r)†) (G z)) = F (((b r)†) (G z))
    rw [hFid]
  rw [hleft, hrightA, hrightB] at hmain
  exact hmain

end

end NLAlib
