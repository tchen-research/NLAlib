import NLAlib.Polynomial.BestApproximation.GapBoundary
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Properness of the interpolation peak-difference map

The finite collision estimate keeps all node gaps away from zero on each bounded
peak-difference sublevel. This proves the actual map proper, once its continuity
on the open node simplex is supplied by the peak charts.
Helper for `lebesgue-constant-lower-bound`.
-/

noncomputable section

open Set Filter

namespace NLAlib

/-- A positive lower bound on every canonical gap implies strict node ordering.
Source: strict monotonicity from adjacent steps; properness helper. -/
theorem mem_interiorNodeSimplex_of_gap_ge {n : ℕ} {t : Fin n → ℝ} {ε : ℝ}
    (hε : 0 < ε) (ht : ∀ i : Fin (n + 1), ε ≤
      canonicalIntervalNodes n t i.succ - canonicalIntervalNodes n t i.castSucc) :
    t ∈ interiorNodeSimplex n := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact sub_pos.mp (hε.trans_le (ht i))

/-- Node configurations with a fixed positive minimum gap form a compact set.
Source: closed linear inequalities inside the finite unit-interval box;
properness helper for `lebesgue-constant-lower-bound`. -/
theorem isCompact_setOf_canonical_gap_ge (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    IsCompact {t : Fin n → ℝ | ∀ i : Fin (n + 1), ε ≤
      canonicalIntervalNodes n t i.succ - canonicalIntervalNodes n t i.castSucc} := by
  have hclosed : IsClosed {t : Fin n → ℝ | ∀ i : Fin (n + 1), ε ≤
      canonicalIntervalNodes n t i.succ - canonicalIntervalNodes n t i.castSucc} := by
    have heq : {t : Fin n → ℝ | ∀ i : Fin (n + 1), ε ≤
        canonicalIntervalNodes n t i.succ - canonicalIntervalNodes n t i.castSucc} =
        ⋂ i : Fin (n + 1), {t | ε ≤
          canonicalIntervalNodes n t i.succ - canonicalIntervalNodes n t i.castSucc} := by
      ext t
      simp
    rw [heq]
    exact isClosed_iInter (fun i => isClosed_le continuous_const
      ((continuous_canonicalIntervalNodes n i.succ).sub
        (continuous_canonicalIntervalNodes n i.castSucc)))
  have hbox : IsCompact (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => (1 : ℝ))) := isCompact_Icc
  apply hbox.of_isClosed_subset hclosed
  intro t ht
  have htu := mem_interiorNodeSimplex_of_gap_ge hε ht
  constructor
  · intro j
    have hj := (canonicalIntervalNodes_mem_Icc htu j.castSucc.succ).1
    simpa only [canonicalIntervalNodes_interior] using hj
  · intro j
    have hj := (canonicalIntervalNodes_mem_Icc htu j.castSucc.succ).2
    simpa only [canonicalIntervalNodes_interior] using hj

/-- Every bounded peak-difference sublevel is compact in the ambient coordinate space.
Source: the exact collision estimate and compact separated-node sets;
helper for `lebesgue-constant-lower-bound`. -/
theorem isCompact_setOf_norm_interpolationPeakDifference_le {n : ℕ}
    (hc : ContinuousOn (interpolationPeakDifference n) (interiorNodeSimplex n))
    {R : ℝ} (hR : 0 ≤ R) :
    IsCompact {t : Fin n → ℝ | t ∈ interiorNodeSimplex n ∧
      ‖interpolationPeakDifference n t‖ ≤ R} := by
  let ε : ℝ := 1 / (2 ^ n * ((n : ℝ) + 1) ^ (n + 1) * (2 * R + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  let S : Set (Fin n → ℝ) := {t | ∀ i : Fin (n + 1), ε ≤
    canonicalIntervalNodes n t i.succ - canonicalIntervalNodes n t i.castSucc}
  have hS := isCompact_setOf_canonical_gap_ge n hε
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hSU : S ⊆ interiorNodeSimplex n := fun _ ht => mem_interiorNodeSimplex_of_gap_ge hε ht
  have hcont : Continuous (fun t : S => ‖interpolationPeakDifference n t‖) :=
    continuousOn_iff_continuous_domRestrict.mp (hc.norm.mono hSU)
  have hsubclosed : IsClosed {t : S | ‖interpolationPeakDifference n t‖ ≤ R} :=
    isClosed_le hcont continuous_const
  have himage := hsubclosed.isCompact.image (continuous_subtype_val : Continuous (fun t : S => (t : Fin n → ℝ)))
  convert himage using 1
  ext t
  constructor
  · intro ht
    have htS : t ∈ S := fun i => canonicalIntervalNodes_gap_ge_of_norm_difference_le ht.1 hR ht.2 i
    exact ⟨⟨t, htS⟩, ht.2, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hSU u.property, hu⟩

/-- The actual peak-difference restriction is proper when its peak charts give continuity.
Source: compact sublevels from finite cardinal products; this discharges the properness
input of the global peak-comparison theorem for the concrete interpolation map.
Helper for `lebesgue-constant-lower-bound`. -/
theorem isProperMap_interpolationPeakDifference {n : ℕ}
    (hc : ContinuousOn (interpolationPeakDifference n) (interiorNodeSimplex n)) :
    IsProperMap (fun t : interiorNodeSimplex n => interpolationPeakDifference n t) := by
  have hcont : Continuous (fun t : interiorNodeSimplex n => interpolationPeakDifference n t) :=
    continuousOn_iff_continuous_domRestrict.mp hc
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hcont, ?_⟩
  intro K hK
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  have hsub : IsCompact {t : interiorNodeSimplex n | ‖interpolationPeakDifference n t‖ ≤ R} := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    convert isCompact_setOf_norm_interpolationPeakDifference_le hc hR.le using 1
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property, hu⟩
    · rintro ⟨ht, hnorm⟩
      exact ⟨⟨t, ht⟩, hnorm, rfl⟩
  exact hsub.of_isClosed_subset (hK.isClosed.preimage hcont)
    (fun t ht => hKR _ ht)

end NLAlib
