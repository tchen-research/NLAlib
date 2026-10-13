import NLAlib.Matrix.Spectral.Weyl
/-!
# Pseudoinverse norm control under a small perturbation

Equal rank and `‖A†‖ ‖B-A‖ < 1` give the exact reciprocal denominator.
Singular-value Weyl supplies the estimate at the last positive singular value;
the rank-zero branch is explicit. Wedin (1973), Stewart–Sun §III.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The exact equal-rank pseudoinverse norm control under a small
perturbation: `‖B⁺‖₂ ≤ ‖A⁺‖₂ / (1 - ‖A⁺‖₂ ‖B - A‖₂)`. Wedin 1973, §4; Stewart–Sun 1990,
Thm III.3.8 (the bound on `‖B⁺‖`); equality of ranks is essential, and rank zero and
arbitrary finite row/column labels are included.
atlas: pseudoinverse-perturbation (partial) -/
theorem specNorm_moorePenroseInverse_le_div_of_rank_eq {A B : Matrix m n ℝ}
    (hr : A.rank=B.rank) (hsmall : specNorm (moorePenroseInverse A)*specNorm (B-A) < 1) :
    specNorm (moorePenroseInverse B) ≤ specNorm (moorePenroseInverse A)/
      (1-specNorm (moorePenroseInverse A)*specNorm (B-A)) := by
  by_cases hz : A.rank=0
  · have hbz : B.rank=0 := hr ▸ hz
    rw [specNorm_moorePenroseInverse_eq A, if_pos hz,
      specNorm_moorePenroseInverse_eq B, if_pos hbz]
    simp
  have hbnz : B.rank ≠ 0 := fun h => hz (hr.trans h)
  let sa := singularValues A (A.rank-1)
  let sb := singularValues B (A.rank-1)
  have hsa : 0 < sa := by
    apply (singularValues_pos_iff A _).mpr
    omega
  have hsb : 0 < sb := by
    apply (singularValues_pos_iff B _).mpr
    omega
  have ha : specNorm (moorePenroseInverse A)=1/sa := by
    rw [specNorm_moorePenroseInverse_eq A, if_neg hz]
  have hb : specNorm (moorePenroseInverse B)=1/sb := by
    rw [specNorm_moorePenroseInverse_eq B, if_neg hbnz, ← hr]
  have hw : sa ≤ sb+specNorm (B-A) := by
    have hh := singularValues_le_singularValues_add_add_specNorm A (B-A) (A.rank-1)
    rwa [add_sub_cancel] at hh
  have haid : specNorm (moorePenroseInverse A)*sa=1 := by rw [ha]; field_simp
  have hbid : specNorm (moorePenroseInverse B)*sb=1 := by rw [hb]; field_simp
  have hmul := mul_le_mul_of_nonneg_left hw
    (mul_nonneg (specNorm_nonneg (moorePenroseInverse A)) (specNorm_nonneg (moorePenroseInverse B)))
  have h1 := congrArg (fun v => specNorm (moorePenroseInverse B)*v) haid
  have h2 := congrArg (fun v => specNorm (moorePenroseInverse A)*v) hbid
  apply (le_div_iff₀ (by linarith : 0 < 1-specNorm (moorePenroseInverse A)*specNorm (B-A))).2
  nlinarith

end NLAlib
