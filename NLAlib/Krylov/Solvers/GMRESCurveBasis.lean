import NLAlib.Krylov.Solvers.GMRESCurveCoordinates
import NLAlib.Matrix.Structured.Companion

/-!
# The explicit change of basis for arbitrary GMRES curves

The columns `[b,e_0,...,e_(n-2)]` form a basis whenever the last coordinate of
`b` is nonzero. The proof permits every earlier coordinate to vanish, which is
essential for convergence curves with stagnation.
Source: Greenbaum--Pták--Strakoš (1996), constructive proof.
-/

noncomputable section
open scoped Matrix
open Matrix Finset
namespace NLAlib

/-- The coordinate shift forming the non-leading columns of the GPS basis. -/
def gmresCurveBasisShift (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if j.val = i.val+1 then 1 else 0

/-- The explicit basis matrix `[b,e_0,...,e_(n-2)]`. -/
def gmresCurveBasis {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec b (Pi.single ⟨0,hn⟩ 1) + gmresCurveBasisShift n

private theorem gmresCurveBasisShift_mulVec {n : ℕ} (v : Fin n → ℂ) (i : Fin n) :
    (gmresCurveBasisShift n *ᵥ v) i =
      if hi : i.val+1 < n then v ⟨i.val+1,hi⟩ else 0 := by
  by_cases hi : i.val+1 < n
  · rw [dif_pos hi]
    change ∑ j : Fin n, (if j.val=i.val+1 then 1 else 0)*v j = _
    rw [sum_eq_single (⟨i.val+1,hi⟩ : Fin n)]
    · simp
    · intro j _ hj
      have hj' : j.val ≠ i.val+1 := by intro he; exact hj (Fin.ext he)
      simp only [if_neg hj',zero_mul]
    · simp
  · rw [dif_neg hi]
    change ∑ j : Fin n, (if j.val=i.val+1 then 1 else 0)*v j = 0
    apply sum_eq_zero
    intro j _
    have hj : j.val ≠ i.val+1 := by intro he; exact hi (he ▸ j.isLt)
    simp only [if_neg hj,zero_mul]

/-- Explicit action of the change of basis. -/
theorem gmresCurveBasis_mulVec {n : ℕ} (hn : 0 < n) (b v : Fin n → ℂ) (i : Fin n) :
    (gmresCurveBasis hn b *ᵥ v) i =
      b i*v ⟨0,hn⟩ + (if hi : i.val+1 < n then v ⟨i.val+1,hi⟩ else 0) := by
  rw [gmresCurveBasis,Matrix.add_mulVec]
  simp only [Pi.add_apply,Matrix.vecMulVec_mulVec,Pi.smul_apply,op_smul_eq_mul,
    single_dotProduct,one_mul,gmresCurveBasisShift_mulVec]

/-- Only the final coordinate needs to be nonzero for the GPS basis to be
invertible; plateaus in the prescribed residual curve are retained.
atlas: gmres-any-convergence-curve (partial) -/
theorem isUnit_gmresCurveBasis {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ)
    (hb : b ⟨n-1,by omega⟩ ≠ 0) : IsUnit (gmresCurveBasis hn b) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hlast := congrFun hvw (⟨n-1,by omega⟩ : Fin n)
  simp only [gmresCurveBasis_mulVec,dif_neg (show ¬n-1+1<n by omega),add_zero] at hlast
  have hzero : v ⟨0,hn⟩ = w ⟨0,hn⟩ := mul_left_cancel₀ hb hlast
  funext j
  by_cases hj : j.val = 0
  · have he : j = ⟨0,hn⟩ := Fin.ext hj
    simpa only [he] using hzero
  · let i : Fin n := ⟨j.val-1,by have := j.isLt; omega⟩
    have hi : i.val+1 < n := by dsimp only [i]; have := j.isLt; omega
    have he : (⟨i.val+1,hi⟩ : Fin n) = j := Fin.ext (by dsimp only [i]; omega)
    have hrow := congrFun hvw i
    rw [gmresCurveBasis_mulVec,gmresCurveBasis_mulVec,dif_pos hi,dif_pos hi,hzero,he] at hrow
    exact add_left_cancel hrow

/-- The first change-of-basis column is the initial residual vector. -/
theorem gmresCurveBasis_mulVec_first {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ) :
    gmresCurveBasis hn b *ᵥ Pi.single ⟨0,hn⟩ (1 : ℂ) = b := by
  funext i
  rw [gmresCurveBasis_mulVec]
  simp only [Pi.single_eq_same,mul_one]
  split_ifs with hi
  · have he : (⟨i.val+1,hi⟩ : Fin n) ≠ ⟨0,hn⟩ := by
      intro hh
      have hval : i.val+1 = 0 := congrArg (fun t : Fin n => t.val) hh
      omega
    simp [he]
  · simp

/-- Every remaining change-of-basis column is the preceding coordinate vector. -/
theorem gmresCurveBasis_mulVec_succ {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ)
    (j : Fin (n-1)) :
    gmresCurveBasis hn b *ᵥ Pi.single ⟨j.val+1,by have := j.isLt; omega⟩ (1 : ℂ) =
      Pi.single ⟨j.val,by have := j.isLt; omega⟩ (1 : ℂ) := by
  funext i
  rw [gmresCurveBasis_mulVec]
  have hj0 : (⟨0,hn⟩ : Fin n) ≠ ⟨j.val+1,by have := j.isLt; omega⟩ := by
    intro he
    have hval : 0 = j.val+1 := congrArg (fun t : Fin n => t.val) he
    omega
  simp only [Pi.single_apply,if_neg hj0,mul_zero,zero_add]
  by_cases hi : i.val+1 < n
  · rw [dif_pos hi]
    have he : (⟨i.val+1,hi⟩ : Fin n) = ⟨j.val+1,by have := j.isLt; omega⟩ ↔
        i = ⟨j.val,by have := j.isLt; omega⟩ := by
      simp only [Fin.ext_iff]
      omega
    simp only [he]
  · rw [dif_neg hi]
    have he : i ≠ (⟨j.val,by have := j.isLt; omega⟩ : Fin n) := by
      intro heq
      have hval : i.val = j.val := congrArg (fun t : Fin n => t.val) heq
      have := j.isLt
      omega
    simp only [if_neg he]

end NLAlib
