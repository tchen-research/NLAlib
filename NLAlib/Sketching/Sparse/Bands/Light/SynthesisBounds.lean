/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.Bands.Light.GramQuadratic
import NLAlib.Matrix.Basic.QuadForm
/-!
# The combined synthesis matrix and its two Gram bounds

Partition of the literal shared-leg proof from sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`.
The original `LightSectorConcrete` import re-exports this unchanged namespace.
Supports the `sparse-ose` moment proof.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace NLAlib.SparseSketch.Light
variable {d m n ell : ℕ}

/-! ### Actual rectangular synthesis matrix and its two Gram matrices -/

/-- Elementary rectangular Gram identity in exact finite coordinates.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordinateEnergy_mulVec_eq_gram
    {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℝ) (x : J → ℝ) :
    sumSq (A.mulVec x) =
      quadForm (A.transpose * A) x := by
  rw [sumSq_eq_dotProduct, quadForm_transpose_mul_self]

/-- The combined synthesis domain is the disjoint union of the individual particle domains.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
abbrev AllDomainIndex (m n ell : ℕ) :=
  Sigma (ParticleDomainIndex m n ell)

/-- The row operator `V(z_1,…,z_ell)=Σ_k V_k z_k` as one literal
rectangular matrix.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def VAllMatrix (F : Frame n d) (ell : ℕ) :
    Matrix (LabelledIndex d m n ell) (AllDomainIndex m n ell) ℝ :=
  fun out z ↦ VMatrix F z.1 out z.2

/-- Coordinates on the disjoint synthesis domain form a family of particle-domain vectors.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def sigmaToFamily (z : AllDomainIndex m n ell → ℝ) :
    DomainFamily m n ell :=
  fun k a ↦ z ⟨k, a⟩

/-- Total energy of a sigma-indexed direct-sum vector is the sum of its exact
dependent component energies.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordinateEnergy_sigma (z : AllDomainIndex m n ell → ℝ) :
    sumSq z = ∑ k, componentEnergy (sigmaToFamily z) k := by
  simp only [sumSq, componentEnergy, sigmaToFamily]
  rw [Fintype.sum_sigma]

/-- The `(k,l)` block pairing in the literal Gram matrix `VᵀV`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def blockGramPairing (F : Frame n d) (ell : ℕ)
    (z : AllDomainIndex m n ell → ℝ) (k l : Fin ell) : ℝ :=
  ∑ a, z ⟨k, a⟩ *
    (((VMatrix F k).transpose * VMatrix F l).mulVec
      (fun b ↦ z ⟨l, b⟩) a)

/-- Expanding the sigma indices in the combined synthesis Gram matrix gives
the sum of its literal typed blocks.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordinateQuadratic_VAll_gram_eq_sum_blocks
    (F : Frame n d) (ell : ℕ) (z : AllDomainIndex m n ell → ℝ) :
    quadForm
        ((VAllMatrix (m := m) F ell).transpose * VAllMatrix F ell) z =
      ∑ k, ∑ l, blockGramPairing F ell z k l := by
  classical
  simp only [quadForm, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.transpose_apply, VAllMatrix,
    blockGramPairing]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _hk
  simp_rw [Fintype.sum_sigma]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A diagonal block contributes exactly `d` times its component energy.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem blockGramPairing_self (F : Frame n d) (ell : ℕ)
    (z : AllDomainIndex m n ell → ℝ) (k : Fin ell) :
    blockGramPairing F ell z k k =
      (d : ℝ) * componentEnergy (sigmaToFamily z) k := by
  classical
  rw [blockGramPairing, transpose_VMatrix_mul]
  simp [componentEnergy, sigmaToFamily, sumSq,
    Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

/-- An off-diagonal literal Gram block is exactly the concrete cross pairing.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem blockGramPairing_cross (F : Frame n d) (ell : ℕ)
    (z : AllDomainIndex m n ell → ℝ) (k l : Fin ell) (hkl : k ≠ l) :
    blockGramPairing F ell z k l =
      crossPairing F (sigmaToFamily z) k l hkl := by
  rw [blockGramPairing, transpose_VMatrix_mul_cross F k l hkl]
  rfl

/-- The full literal Gram quadratic is exactly the previously estimated
shared-leg block form.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_blockGramPairing_eq_sharedLeg (F : Frame n d) (ell : ℕ)
    (z : AllDomainIndex m n ell → ℝ) :
    (∑ k, ∑ l, blockGramPairing F ell z k l) =
      sharedLegGramQuadratic F (sigmaToFamily z) := by
  classical
  have hrow (k : Fin ell) :
      (∑ l, blockGramPairing F ell z k l) =
        (d : ℝ) * componentEnergy (sigmaToFamily z) k +
          ∑ l ∈ Finset.univ.erase k,
            crossPairingTotal F (sigmaToFamily z) k l := by
    calc
      (∑ l, blockGramPairing F ell z k l) =
          (∑ l ∈ Finset.univ.erase k, blockGramPairing F ell z k l) +
            blockGramPairing F ell z k k :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ k)).symm
      _ = blockGramPairing F ell z k k +
          ∑ l ∈ Finset.univ.erase k, blockGramPairing F ell z k l :=
        add_comm _ _
      _ = (d : ℝ) * componentEnergy (sigmaToFamily z) k +
          ∑ l ∈ Finset.univ.erase k,
            crossPairingTotal F (sigmaToFamily z) k l := by
        rw [blockGramPairing_self]
        congr 1
        apply Finset.sum_congr rfl
        intro l hl
        have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
        have hkl : k ≠ l := Ne.symm hlk
        rw [blockGramPairing_cross F ell z k l hkl]
        simp [crossPairingTotal, hkl]
  simp_rw [hrow]
  unfold sharedLegGramQuadratic
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The combined synthesis Gram quadratic form equals the shared-leg Gram quadratic form.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem coordinateQuadratic_VAll_gram_eq_sharedLeg
    (F : Frame n d) (ell : ℕ) (z : AllDomainIndex m n ell → ℝ) :
    quadForm
        ((VAllMatrix (m := m) F ell).transpose * VAllMatrix F ell) z =
      sharedLegGramQuadratic F (sigmaToFamily z) := by
  rw [coordinateQuadratic_VAll_gram_eq_sum_blocks,
    sum_blockGramPairing_eq_sharedLeg]

/-- The combined concrete synthesis map obeys the exact `d + ell - 1`
Euclidean energy bound.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem VAllMatrix_energy_le (F : Frame n d) (ell : ℕ)
    (z : AllDomainIndex m n ell → ℝ) (hell : 1 ≤ ell) :
    sumSq ((VAllMatrix (m := m) F ell).mulVec z) ≤
      ((d : ℝ) + (ell : ℝ) - 1) * sumSq z := by
  rw [coordinateEnergy_mulVec_eq_gram,
    coordinateQuadratic_VAll_gram_eq_sharedLeg,
    coordinateEnergy_sigma]
  exact sharedLegGramQuadratic_le F (sigmaToFamily z) hell

/-- Finite-coordinate Cauchy--Schwarz in the exact normalization used here.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordinate_dot_sq_le {I : Type*} [Fintype I]
    (x y : I → ℝ) :
    (∑ i, x i * y i) ^ 2 ≤ sumSq x * sumSq y := by
  simpa [sumSq] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ) x y)

/-- A synthesis energy bound implies the same one-sided quadratic bound for
its positive row Gram matrix.  The cancellation is proved directly from
finite-coordinate Cauchy--Schwarz.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gramQuadratic_le_of_energy_le
    {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ z : J → ℝ,
      sumSq (A.mulVec z) ≤ c * sumSq z)
    (x : I → ℝ) :
    quadForm (A * A.transpose) x ≤
      c * sumSq x := by
  let z : J → ℝ := A.transpose.mulVec x
  have hgram : sumSq z = quadForm (A * A.transpose) x := by
    simpa [z] using coordinateEnergy_mulVec_eq_gram A.transpose x
  have hinner : sumSq z = ∑ i, x i * A.mulVec z i := by
    calc
      sumSq z = quadForm (A * A.transpose) x := hgram
      _ = ∑ i, x i * A.mulVec z i := by
        simp only [quadForm, dotProduct]
        rw [Matrix.mulVec_mulVec]
  have hcs : sumSq z ^ 2 ≤
      sumSq x * sumSq (A.mulVec z) := by
    rw [hinner]
    exact coordinate_dot_sq_le x (A.mulVec z)
  have hmul : sumSq x * sumSq (A.mulVec z) ≤
      sumSq x * (c * sumSq z) :=
    mul_le_mul_of_nonneg_left (hA z) (sumSq_nonneg x)
  have hchain : sumSq z ^ 2 ≤
      sumSq x * (c * sumSq z) := hcs.trans hmul
  have hznonneg := sumSq_nonneg z
  have hbound : sumSq z ≤ c * sumSq x := by
    by_cases hz : sumSq z = 0
    · rw [hz]
      exact mul_nonneg hc (sumSq_nonneg x)
    · have hzpos : 0 < sumSq z := lt_of_le_of_ne hznonneg (Ne.symm hz)
      nlinarith
  rw [← hgram]
  exact hbound

/-- The labelled-particle operator `Σ_k Q_k`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def labelledG (F : Frame n d) (ell : ℕ) :
    Matrix (LabelledIndex d m n ell) (LabelledIndex d m n ell) ℝ :=
  ∑ k, qSlot F k

/-- The labelled shared-leg operator is invariant under simultaneous slot relabelling.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem labelledG_relabelSlots (F : Frame n d) (ell : ℕ)
    (pi : Equiv.Perm (Fin ell))
    (out inp : LabelledIndex d m n ell) :
    labelledG F ell (relabelSlots pi out) (relabelSlots pi inp) =
      labelledG F ell out inp := by
  classical
  simp only [labelledG, Matrix.sum_apply, qSlot_relabelSlots]
  exact Equiv.sum_comp pi (fun k ↦ qSlot F k out inp)

/-- Each one-slot shared-leg operator is symmetric.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem qSlot_transpose (F : Frame n d) (k : Fin ell) :
    (qSlot (m := m) F k).transpose = qSlot F k := by
  ext out inp
  simp only [Matrix.transpose_apply, qSlot]
  by_cases hdom : domainOfWord k out.2 = domainOfWord k inp.2
  · rw [if_pos hdom.symm, if_pos hdom]
    ring
  · have hrev : domainOfWord k inp.2 ≠ domainOfWord k out.2 :=
      fun h ↦ hdom h.symm
    rw [if_neg hrev, if_neg hdom]

/-- The labelled shared-leg operator is symmetric.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem labelledG_transpose (F : Frame n d) (ell : ℕ) :
    (labelledG (m := m) F ell).transpose = labelledG F ell := by
  rw [labelledG, Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  exact qSlot_transpose (m := m) F k

/-- The labelled operator is literally `V Vᵀ`, not just spectrally
equivalent to it.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem VAllMatrix_mul_transpose (F : Frame n d) (ell : ℕ) :
    VAllMatrix (m := m) F ell * (VAllMatrix F ell).transpose =
      labelledG F ell := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, VAllMatrix,
    labelledG, Matrix.sum_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _hk
  have h := congrFun (congrFun (VMatrix_mul_transpose (m := m) F k) out) inp
  simpa [Matrix.mul_apply] using h

/-- The labelled shared-leg operator is Hermitian.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem labelledG_isHermitian (F : Frame n d) (ell : ℕ) :
    (labelledG (m := m) F ell).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  change (labelledG (m := m) F ell).transpose = labelledG F ell
  exact labelledG_transpose F ell

/-- Positivity of the labelled shared-leg matrix, in literal coordinates.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem labelledG_coordinateQuadratic_nonneg (F : Frame n d) (ell : ℕ)
    (x : LabelledIndex d m n ell → ℝ) :
    0 ≤ quadForm (labelledG F ell) x := by
  rw [← VAllMatrix_mul_transpose]
  have hgram :
      sumSq
          ((VAllMatrix (m := m) F ell).transpose.mulVec x) =
        quadForm
          (VAllMatrix (m := m) F ell *
            (VAllMatrix (m := m) F ell).transpose) x := by
    simpa using coordinateEnergy_mulVec_eq_gram
      (VAllMatrix (m := m) F ell).transpose x
  rw [← hgram]
  exact sumSq_nonneg _

/-- The concrete labelled-particle Gram operator obeys the sharp light-sector
constant `d + ell - 1` as an actual coordinate quadratic-form estimate.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem labelledG_coordinateQuadratic_le (F : Frame n d) (ell : ℕ)
    (x : LabelledIndex d m n ell → ℝ) (hell : 1 ≤ ell) :
    quadForm (labelledG F ell) x ≤
      ((d : ℝ) + (ell : ℝ) - 1) * sumSq x := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hc : 0 ≤ (d : ℝ) + (ell : ℝ) - 1 := by
    linarith
  rw [← VAllMatrix_mul_transpose]
  exact gramQuadratic_le_of_energy_le
    (VAllMatrix (m := m) F ell)
    ((d : ℝ) + (ell : ℝ) - 1) hc
    (fun z ↦ VAllMatrix_energy_le F ell z hell) x

/-- Final L2 operator-norm form of the concrete labelled shared-leg bound.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem labelledG_norm_le (F : Frame n d) (ell : ℕ) (hell : 1 ≤ ell) :
    ‖labelledG (m := m) F ell‖ ≤ (d : ℝ) + (ell : ℝ) - 1 := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hc : 0 ≤ (d : ℝ) + (ell : ℝ) - 1 := by
    linarith
  apply (specNorm_le_iff_abs_dotProduct_mulVec_le
    (labelledG (m := m) F ell) (labelledG_isHermitian F ell)
    ((d : ℝ) + (ell : ℝ) - 1) hc).2
  intro x
  have hupper := labelledG_coordinateQuadratic_le F ell x hell
  rw [sumSq_eq_dotProduct] at hupper
  exact (abs_of_nonneg (labelledG_coordinateQuadratic_nonneg F ell x)).trans_le hupper

/-- Grade-envelope form: whenever a nonzero light count `ell` occurs inside
total grade `nu`, the labelled shared-leg operator is bounded by `d + nu`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem labelledG_norm_le_grade (F : Frame n d) (ell nu : ℕ)
    (hell : 1 ≤ ell) (hle : ell ≤ nu) :
    ‖labelledG (m := m) F ell‖ ≤ (d : ℝ) + (nu : ℝ) := by
  calc
    ‖labelledG (m := m) F ell‖ ≤ (d : ℝ) + (ell : ℝ) - 1 :=
      labelledG_norm_le F ell hell
    _ ≤ (d : ℝ) + (nu : ℝ) := by
      have hleR : (ell : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hle
      linarith

end NLAlib.SparseSketch.Light
