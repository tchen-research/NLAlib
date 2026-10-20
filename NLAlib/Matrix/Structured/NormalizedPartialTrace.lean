import NLAlib.Matrix.Structured.KroneckerNormRank
import NLAlib.Matrix.Norms.DependentBlockDiagonal
import NLAlib.Matrix.Basic.NormalizedTrace
import Mathlib.Data.Matrix.Basis

/-! # Actual normalized partial trace in finite matrix tensor coordinates

The coefficient-side partial trace averages the actual ensemble diagonal.
Its entry probes have squared Frobenius norm equal to the ensemble dimension;
this preserves the essential inverse-dimension gradient normalization.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Kronecker
namespace NLAlib
variable {d n : Type*} [Fintype d] [Fintype n] [DecidableEq d] [DecidableEq n]

/-- Average the actual ensemble diagonal blocks of a finite tensor matrix.
The empty ensemble has normalized partial trace zero. -/
def normalizedPartialTrace (T : Matrix (d×n) (d×n) ℂ) : Matrix d d ℂ :=
  fun a b => (Fintype.card n : ℂ)⁻¹*∑ r : n, T (a,r) (b,r)

/-- Each actual normalized partial-trace entry is the ordinary matrix trace
against its rank-one coefficient probe and ensemble identity. -/
theorem normalizedPartialTrace_apply_eq_trace
    (T : Matrix (d×n) (d×n) ℂ) (a b : d) :
    normalizedPartialTrace T a b = (Fintype.card n : ℂ)⁻¹*
      (((Matrix.single b a 1 : Matrix d d ℂ)⊗ₖ(1 : Matrix n n ℂ))*T).trace := by
  simp [normalizedPartialTrace,Matrix.trace,Matrix.diag,Matrix.mul_apply,
    Fintype.sum_prod_type,Matrix.kroneckerMap_apply,Matrix.single_apply,
    Matrix.one_apply,ite_and]

omit [Fintype d] [DecidableEq d] in
/-- The true normalized tensor partial trace returns the coefficient matrix
when the ensemble dimension is positive. -/
theorem normalizedPartialTrace_kronecker_one [Nonempty n] (Q : Matrix d d ℂ) :
    normalizedPartialTrace (Q⊗ₖ(1 : Matrix n n ℂ))=Q := by
  have hN : (Fintype.card n : ℂ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext a b
  simp [normalizedPartialTrace,hN]

omit [DecidableEq d] [DecidableEq n] in
/-- Taking normalized trace after the actual normalized partial trace is
exactly the original normalized tensor-matrix trace. The empty dimension
conventions agree on both sides. -/
theorem normalizedTrace_normalizedPartialTrace (T : Matrix (d×n) (d×n) ℂ) :
    normalizedTrace (normalizedPartialTrace T)=normalizedTrace T := by
  simp only [normalizedTrace,normalizedPartialTrace,Matrix.trace,Matrix.diag,
    Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,← Finset.mul_sum]
  ring

open scoped Matrix.Norms.L2Operator in
/-- The actual tensor probe for one normalized partial-trace entry has
squared Frobenius norm exactly N, including an empty ensemble. -/
theorem frobSq_single_kronecker_one (a b : d) :
    frobSq ((Matrix.single a b 1 : Matrix d d ℂ)⊗ₖ(1 : Matrix n n ℂ))=
      (Fintype.card n : ℝ) := by
  simp [frobSq_eq_sum_norm_sq,Fintype.sum_prod_type,Matrix.kroneckerMap_apply,
    Matrix.single_apply,Matrix.one_apply,ite_and,apply_ite]
  have he : Finset.univ.filter (fun x : d×n => a=x.1)=
      Finset.univ.image (fun r : n => (a,r)) := by
    ext x
    simp [Prod.ext_iff,eq_comm]
  rw [he,Finset.card_image_of_injective _ (fun u v h => congrArg Prod.snd h)]
  exact Finset.card_univ

open scoped Matrix.Norms.L2Operator in
/-- The actual normalized partial trace is a native continuous linear map. -/
def normalizedPartialTraceCLM :
    Matrix (d×n) (d×n) ℂ →L[ℂ] Matrix d d ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := normalizedPartialTrace
      map_add' := by intro T U; ext a b; simp [normalizedPartialTrace,Finset.sum_add_distrib,mul_add]
      map_smul' := by
        intro c T
        ext a b
        simp [normalizedPartialTrace,← Finset.mul_sum,mul_left_comm] }

omit [DecidableEq d] [DecidableEq n] in
open scoped Matrix.Norms.L2Operator in
/-- The native partial-trace map evaluates to the literal normalized diagonal
average, without an assumed averaging or marginal-law specification. -/
@[simp] theorem normalizedPartialTraceCLM_apply (T : Matrix (d×n) (d×n) ℂ) :
    normalizedPartialTraceCLM T=normalizedPartialTrace T := rfl

open scoped Matrix.Norms.L2Operator in
/-- Averaging the actual diagonal ensemble compressions is a contraction
for the genuine spectral norm. Empty matrix dimensions are included. -/
theorem specNorm_normalizedPartialTrace_le (T : Matrix (d×n) (d×n) ℂ) :
    specNorm (normalizedPartialTrace T)≤specNorm T := by
  rcases isEmpty_or_nonempty n with hn|hn
  · let := hn
    have he : normalizedPartialTrace T=0 := by ext a b; simp [normalizedPartialTrace]
    rw [he,specNorm_zero]
    exact specNorm_nonneg _
  · let := hn
    have hN : (Fintype.card n : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have he : normalizedPartialTrace T=(Fintype.card n : ℂ)⁻¹ •
        ∑ r : n, T.submatrix (fun a : d => (a,r)) (fun b : d => (b,r)) := by
      ext a b
      simp [normalizedPartialTrace,Matrix.sum_apply,Matrix.submatrix_apply]
    rw [he,specNorm_eq_norm,norm_smul,norm_inv,Complex.norm_natCast]
    calc
      _ ≤ (Fintype.card n : ℝ)⁻¹*∑ r : n,
          ‖T.submatrix (fun a : d => (a,r)) (fun b : d => (b,r))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (Fintype.card n : ℝ)⁻¹*∑ _ : n, specNorm T := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro r _
        rw [← specNorm_eq_norm]
        exact specNorm_submatrix_le T _ _
          (fun a b h => congrArg Prod.fst h) (fun a b h => congrArg Prod.fst h)
      _ = _ := by simp [hN]


omit [DecidableEq d] in
/-- Left multiplication by an actual coefficient tensor commutes with the
genuine normalized ensemble partial trace. No ensemble dimension premise
is needed, since both sides vanish for an empty ensemble. -/
theorem normalizedPartialTrace_kronecker_one_mul
    (A : Matrix d d ℂ) (T : Matrix (d×n) (d×n) ℂ) :
    normalizedPartialTrace ((A⊗ₖ(1 : Matrix n n ℂ))*T)=
      A*normalizedPartialTrace T := by
  ext a b
  simp only [normalizedPartialTrace,Matrix.mul_apply,Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  simp only [Matrix.one_apply,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,
    ]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp [mul_ite,mul_left_comm]

omit [DecidableEq d] in
/-- Right multiplication by a coefficient tensor also commutes with the
actual normalized ensemble partial trace. -/
theorem normalizedPartialTrace_mul_kronecker_one
    (T : Matrix (d×n) (d×n) ℂ) (A : Matrix d d ℂ) :
    normalizedPartialTrace (T*(A⊗ₖ(1 : Matrix n n ℂ)))=
      normalizedPartialTrace T*A := by
  ext a b
  simp only [normalizedPartialTrace,Matrix.mul_apply,Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  simp only [Matrix.one_apply,mul_ite,mul_one,mul_zero,
    ]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro r _
  simp [mul_ite,mul_left_comm,mul_comm]


open scoped Matrix.Norms.L2Operator in
/-- The genuine normalized partial-trace continuous linear map has norm at
most one, including empty matrix dimensions. -/
theorem norm_normalizedPartialTraceCLM_le_one :
    ‖normalizedPartialTraceCLM (d := d) (n := n)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  simpa only [one_mul,normalizedPartialTraceCLM_apply,← specNorm_eq_norm] using
    specNorm_normalizedPartialTrace_le T

omit [Fintype d] [DecidableEq n] [DecidableEq d] in
/-- Actual normalized partial trace commutes with the adjoint, including empty dimensions. -/
theorem normalizedPartialTrace_conjTranspose (T : Matrix (d×n) (d×n) ℂ) :
    normalizedPartialTrace Tᴴ=(normalizedPartialTrace T)ᴴ := by
  ext a b
  simp [normalizedPartialTrace,Matrix.conjTranspose_apply]

end NLAlib
