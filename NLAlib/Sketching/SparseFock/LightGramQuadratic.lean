/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightCrossContraction

/-!
# The dimension-plus-particle-count shared-leg quadratic estimate

Partition of the literal shared-leg proof from sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`.
The original `LightSectorConcrete` import re-exports this unchanged namespace.
Supports the `sparse-ose` moment proof.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace NLAlib.SparseFock.LightSectorConcrete
open ParsevalFrame LocalOperator FiniteOperator ExternalOperator FiniteHilbert
variable {d m n ell : ℕ}

/-! ### The concrete `d + ell - 1` block-Gram estimate -/

/-- A genuinely dependent direct-sum vector: its `k`th component lives in
the exact domain `D_k`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev DomainFamily (m n ell : ℕ) :=
  (k : Fin ell) → ParticleDomainIndex m n ell k → ℝ

/-- The energy of one domain-family component is the sum of its squared coordinates.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def componentEnergy (z : DomainFamily m n ell) (k : Fin ell) : ℝ :=
  coordinateEnergy (z k)

/-- The off-diagonal pairing applies the concrete cross matrix between two component vectors.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def crossPairing (F : Frame n d) (z : DomainFamily m n ell)
    (k l : Fin ell) (hkl : k ≠ l) : ℝ :=
  ∑ a, z k a * (crossMatrix F k l hkl).mulVec (z l) a

/-- `2ab ≤ a²+b²`, summed over the exact typed cross map, followed by
the already-proved `U Uᵀ` contraction.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem two_crossPairing_le (F : Frame n d) (z : DomainFamily m n ell)
    (k l : Fin ell) (hkl : k ≠ l) :
    2 * crossPairing F z k l hkl ≤
      componentEnergy z k + componentEnergy z l := by
  let w : ParticleDomainIndex m n ell k → ℝ :=
    (crossMatrix F k l hkl).mulVec (z l)
  have hpoint (a : ParticleDomainIndex m n ell k) :
      2 * z k a * w a ≤ (z k a) ^ 2 + (w a) ^ 2 := by
    nlinarith [sq_nonneg (z k a - w a)]
  have hsum :
      2 * crossPairing F z k l hkl ≤
        componentEnergy z k + coordinateEnergy w := by
    calc
      2 * crossPairing F z k l hkl = ∑ a, 2 * z k a * w a := by
        simp only [crossPairing, w, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ ≤ ∑ a, ((z k a) ^ 2 + (w a) ^ 2) :=
        Finset.sum_le_sum fun a _ha ↦ hpoint a
      _ = componentEnergy z k + coordinateEnergy w := by
        simp [componentEnergy, coordinateEnergy, Finset.sum_add_distrib]
  have hcontract : coordinateEnergy w ≤ componentEnergy z l := by
    exact crossMatrix_energy_le F k l hkl (z l)
  linarith

/-- An off-diagonal cross pairing is bounded by half the sum of the two component energies.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem crossPairing_le_half (F : Frame n d) (z : DomainFamily m n ell)
    (k l : Fin ell) (hkl : k ≠ l) :
    crossPairing F z k l hkl ≤
      (componentEnergy z k + componentEnergy z l) / 2 := by
  linarith [two_crossPairing_le F z k l hkl]

/-- The total cross pairing uses the off-diagonal pairing and is zero on equal slots.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def crossPairingTotal (F : Frame n d) (z : DomainFamily m n ell)
    (k l : Fin ell) : ℝ :=
  if hkl : k ≠ l then crossPairing F z k l hkl else 0

/-- Every total cross pairing is bounded by half the two component energies.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem crossPairingTotal_le_half (F : Frame n d) (z : DomainFamily m n ell)
    (k l : Fin ell) (hkl : k ≠ l) :
    crossPairingTotal F z k l ≤
      (componentEnergy z k + componentEnergy z l) / 2 := by
  simp only [crossPairingTotal, dif_pos hkl]
  exact crossPairing_le_half F z k l hkl

/-- The literal quadratic form of the dependent block matrix whose diagonal
blocks are `V_kᵀV_k=dI` and whose off-diagonal blocks are the proved concrete
cross matrices.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def sharedLegGramQuadratic (F : Frame n d) (z : DomainFamily m n ell) : ℝ :=
  (d : ℝ) * ∑ k, componentEnergy z k +
    ∑ k, ∑ l ∈ Finset.univ.erase k,
      crossPairingTotal F z k l

/-- Concrete finite-coordinate block-Gram bound.  There is no assumed
cross-map estimate: every cross term invokes `crossMatrix_energy_le`, already
proved from Parseval above.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sharedLegGramQuadratic_le (F : Frame n d) (z : DomainFamily m n ell)
    (hell : 1 ≤ ell) :
    sharedLegGramQuadratic F z ≤
      ((d : ℝ) + (ell : ℝ) - 1) * ∑ k, componentEnergy z k := by
  have hcross :
      (∑ k, ∑ l ∈ Finset.univ.erase k,
        crossPairingTotal F z k l) ≤
        ((ell : ℝ) - 1) * ∑ k, componentEnergy z k := by
    apply LightSectorAbstract.offDiagonal_sum_le hell
    intro k l hkl
    exact crossPairingTotal_le_half F z k l hkl
  unfold sharedLegGramQuadratic
  calc
    (d : ℝ) * ∑ k, componentEnergy z k +
        ∑ k, ∑ l ∈ Finset.univ.erase k,
          crossPairingTotal F z k l ≤
      (d : ℝ) * ∑ k, componentEnergy z k +
        ((ell : ℝ) - 1) * ∑ k, componentEnergy z k :=
      add_le_add_right hcross _
    _ = ((d : ℝ) + (ell : ℝ) - 1) *
        ∑ k, componentEnergy z k := by ring

end NLAlib.SparseFock.LightSectorConcrete
