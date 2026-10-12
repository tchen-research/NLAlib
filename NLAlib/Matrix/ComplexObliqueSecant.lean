import NLAlib.Matrix.ComplexIdempotentRealForm
import NLAlib.Matrix.ComplexFrameTransport
import NLAlib.Matrix.ObliqueProjectionSecant

/-!
# Complex oblique projection norms and principal angles

The norm is the secant of the largest actual principal angle between the
complex range and the orthogonal complement of the complex kernel.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Principal angles between equal-dimensional complex frames are the
arccosines of the descending actual singular values of their conjugate
overlap. Stewart–Sun, Section I.5; complex CS and oblique projection helper. -/
def complexPrincipalAnglesFintype {m r : Type*} [Fintype m] [Fintype r] [DecidableEq r]
    (Q W : Matrix m r ℂ) : Fin (Fintype.card r) → ℝ :=
  fun i => Real.arccos ((Qᴴ * W).toEuclideanLin.singularValues i)

/-- Every positive-rank complex idempotent has unitary-column frames for
its actual range and kernel orthogonal complement. Their largest actual
principal angle is strictly below pi/2 and its secant is exactly the
Euclidean operator norm. Horn–Johnson 2013, Corollary 3.4.3.3; the identity
at positive dimension is included, and rank zero is excluded precisely
because it has no largest principal angle.
atlas: cs-decomposition (partial) -/
theorem exists_complex_range_kernel_frames_norm_eq_secant {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (hP : IsIdempotentElem P)
    (hr : 0 < P.rank) :
    ∃ Q W : Matrix n (Fin P.rank) ℂ,
      Qᴴ * Q = 1 ∧ Wᴴ * W = 1 ∧
      LinearMap.range Q.toEuclideanLin = LinearMap.range P.toEuclideanLin ∧
      LinearMap.range W.toEuclideanLin = (LinearMap.ker P.toEuclideanLin)ᗮ ∧
      let θ := complexPrincipalAnglesFintype W Q ⟨P.rank - 1, by simpa using Nat.sub_lt hr Nat.one_pos⟩
      (∀ i, complexPrincipalAnglesFintype W Q i ≤ θ) ∧
      θ < Real.pi / 2 ∧ ‖P‖ = 1 / Real.cos θ := by
  obtain ⟨U, R, hR, hPR, _, hRank, hNorm, _⟩ := exists_real_idempotent_unitary_similarity P hP
  have hrR : 0 < R.rank := by omega
  obtain ⟨Q₀, W₀, hQ₀, hW₀, hRange, hRow, hAngles⟩ := exists_range_kernel_frames_specNorm_eq_secant R hR hrR
  let Q := (U : Matrix n n ℂ) * Q₀.map Complex.ofReal
  let W := (U : Matrix n n ℂ) * W₀.map Complex.ofReal
  have hU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have hGram (F : Matrix n (Fin R.rank) ℝ) (hF : HasOrthonormalCols F) :
      ((U : Matrix n n ℂ) * F.map Complex.ofReal)ᴴ *
        ((U : Matrix n n ℂ) * F.map Complex.ofReal) = 1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ) (F.map Complex.ofReal),
      hU, Matrix.one_mul, conjTranspose_map_ofReal, ← map_ofReal_mul, hF]
    simp
  have hQrange : LinearMap.range Q.toEuclideanLin = LinearMap.range P.toEuclideanLin :=
    range_unitary_mul_eq_of_similarity U P (R.map Complex.ofReal) (Q₀.map Complex.ofReal)
      hPR (range_toEuclideanLin_map_ofReal_eq Q₀ R hRange)
  have hRadj : Rᵀ.toEuclideanLin = LinearMap.adjoint R.toEuclideanLin := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint R
  have hRow' : LinearMap.range W₀.toEuclideanLin = LinearMap.range Rᵀ.toEuclideanLin := by
    rw [hRow, hRadj, LinearMap.orthogonal_ker]
  have hPRadj : Pᴴ = (U : Matrix n n ℂ) * Rᵀ.map Complex.ofReal * (U : Matrix n n ℂ)ᴴ := by
    rw [hPR]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      conjTranspose_map_ofReal, Matrix.mul_assoc]
  have hWrange : LinearMap.range W.toEuclideanLin = (LinearMap.ker P.toEuclideanLin)ᗮ := by
    calc
      _ = LinearMap.range Pᴴ.toEuclideanLin :=
        range_unitary_mul_eq_of_similarity U Pᴴ (Rᵀ.map Complex.ofReal) (W₀.map Complex.ofReal)
          hPRadj (range_toEuclideanLin_map_ofReal_eq W₀ Rᵀ hRow')
      _ = _ := by rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.orthogonal_ker]
  have hOverlap : Wᴴ * Q = (W₀ᵀ * Q₀).map Complex.ofReal := by
    simp only [W, Q, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ) (Q₀.map Complex.ofReal),
      hU, Matrix.one_mul, conjTranspose_map_ofReal, ← map_ofReal_mul]
  have hAngle (i : Fin (Fintype.card (Fin R.rank))) :
      complexPrincipalAnglesFintype W Q i = principalAnglesFintype W₀ Q₀ i := by
    simp only [complexPrincipalAnglesFintype, principalAnglesFintype, hOverlap,
      toEuclideanLin_singularValues_map_ofReal, singularValues_reindex_eq_toEuclideanLin_singularValues]
  have hFinal : ∃ Q W : Matrix n (Fin R.rank) ℂ,
      Qᴴ * Q = 1 ∧ Wᴴ * W = 1 ∧
      LinearMap.range Q.toEuclideanLin = LinearMap.range P.toEuclideanLin ∧
      LinearMap.range W.toEuclideanLin = (LinearMap.ker P.toEuclideanLin)ᗮ ∧
      let θ := complexPrincipalAnglesFintype W Q ⟨R.rank - 1, by simpa using Nat.sub_lt hrR Nat.one_pos⟩
      (∀ i, complexPrincipalAnglesFintype W Q i ≤ θ) ∧
      θ < Real.pi / 2 ∧ ‖P‖ = 1 / Real.cos θ := by
    refine ⟨Q, W, hGram Q₀ hQ₀, hGram W₀ hW₀, hQrange, hWrange, ?_⟩
    dsimp only at hAngles ⊢
    simp only [hAngle, hNorm]
    exact hAngles
  let G (r : ℕ) : Prop := ∀ hr : 0 < r,
    ∃ Q W : Matrix n (Fin r) ℂ,
      Qᴴ * Q = 1 ∧ Wᴴ * W = 1 ∧
      LinearMap.range Q.toEuclideanLin = LinearMap.range P.toEuclideanLin ∧
      LinearMap.range W.toEuclideanLin = (LinearMap.ker P.toEuclideanLin)ᗮ ∧
      let θ := complexPrincipalAnglesFintype W Q ⟨r - 1, by simpa using Nat.sub_lt hr Nat.one_pos⟩
      (∀ i, complexPrincipalAnglesFintype W Q i ≤ θ) ∧
      θ < Real.pi / 2 ∧ ‖P‖ = 1 / Real.cos θ
  have hGR : G R.rank := fun _ => hFinal
  have hGP : G P.rank := Eq.mp (congrArg G hRank.symm) hGR
  exact hGP hr

end NLAlib
