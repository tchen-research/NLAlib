/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.GlobalBands
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Named physical band families

The paper uses the names `L`, `X`, `Y`, and `H` for the sixteen oriented
local products.  `GlobalBands` already proves the exhaustive nine-cell
partition; this file identifies every cell with the exact named sum appearing
in equations (light-heavy-defs), (mixed-defs), and (exact-inventory).
-/

namespace NLAlib.SparseFock.NamedBands

open BandInventory GlobalBands ExternalOperator

noncomputable section

variable {d m n : ℕ}

/-- A physical sparse-Fock operator is a finite matrix on external-coordinate and pattern indices.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev Physical (d m n : ℕ) := FullOp d m n

/-- A named two-leg word sums its physical distinct-column terms over all rows.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def wordSum (m : ℕ) (u : Fin n → Fin d → ℝ) (a b : Leg) :
    Physical d m n :=
  physicalWordSum m u (a, b)

/-- The light-light raising band consists of two light creation legs.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Lplus (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pUp .pUp

/-- The light-light preserving band sums the two light creation-annihilation orientations.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Lzero (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pUp .pDown + wordSum m u .pDown .pUp

/-- The light-light lowering band consists of two light annihilation legs.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Lminus (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pDown .pDown

/-- The heavy-heavy raising band consists of two heavy creation legs.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Hplus (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rUp .rUp

/-- The heavy-heavy preserving band sums the two heavy creation-annihilation orientations.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Hzero (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rUp .rDown + wordSum m u .rDown .rUp

/-- The heavy-heavy lowering band consists of two heavy annihilation legs.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Hminus (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rDown .rDown

/-- The first mixed raising band has light creation followed by heavy creation.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Xplus (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pUp .rUp

/-- The second mixed raising band has heavy creation followed by light creation.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Yplus (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rUp .pUp

/-- The first mixed preserving band has light creation followed by heavy annihilation.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Xzero (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pUp .rDown

/-- The second mixed preserving band has heavy annihilation followed by light creation.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Yzero (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rDown .pUp

/-- The first mixed lowering band is the ordered adjoint of the first raising band.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def XplusAdj (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rDown .pDown

/-- The second mixed lowering band is the ordered adjoint of the second raising band.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def YplusAdj (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pDown .rDown

/-- The first mixed preserving adjoint reverses the light-heavy orientation.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def XzeroAdj (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rUp .pDown

/-- The second mixed preserving adjoint reverses the heavy-light orientation.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def YzeroAdj (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pDown .rUp

/-- The raising lightLight inventory cell equals its named physical band family.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem family_plus_lightLight (u : Fin n → Fin d → ℝ) :
    family m u .plus .lightLight = Lplus m u := by
  rw [family, show wordsIn .plus .lightLight = {(.pUp, .pUp)} by decide]
  simp [Lplus, wordSum]

/-- The raising lightHeavy inventory cell equals its named physical band family.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem family_plus_lightHeavy (u : Fin n → Fin d → ℝ) :
    family m u .plus .lightHeavy = Xplus m u + Yplus m u := by
  rw [family, show wordsIn .plus .lightHeavy = {(.pUp, .rUp), (.rUp, .pUp)} by decide]
  simp [Xplus, Yplus, wordSum]

/-- The raising heavyHeavy inventory cell equals its named physical band family.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem family_plus_heavyHeavy (u : Fin n → Fin d → ℝ) :
    family m u .plus .heavyHeavy = Hplus m u := by
  rw [family, show wordsIn .plus .heavyHeavy = {(.rUp, .rUp)} by decide]
  simp [Hplus, wordSum]

/-- The preserving lightLight inventory cell equals its named physical band family.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem family_zero_lightLight (u : Fin n → Fin d → ℝ) :
    family m u .zero .lightLight = Lzero m u := by
  rw [family, show wordsIn .zero .lightLight =
    {(.pUp, .pDown), (.pDown, .pUp)} by decide]
  simp [Lzero, wordSum, add_comm]

/-- The preserving lightHeavy inventory cell equals its named physical band family.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem family_zero_lightHeavy (u : Fin n → Fin d → ℝ) :
    family m u .zero .lightHeavy =
      Xzero m u + XzeroAdj m u + Yzero m u + YzeroAdj m u := by
  rw [family, show wordsIn .zero .lightHeavy =
    {(.pUp, .rDown), (.rUp, .pDown), (.rDown, .pUp), (.pDown, .rUp)} by decide]
  simp [Xzero, XzeroAdj, Yzero, YzeroAdj, wordSum]
  abel

/-- The preserving heavyHeavy inventory cell equals its named physical band family.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem family_zero_heavyHeavy (u : Fin n → Fin d → ℝ) :
    family m u .zero .heavyHeavy = Hzero m u := by
  rw [family, show wordsIn .zero .heavyHeavy =
    {(.rUp, .rDown), (.rDown, .rUp)} by decide]
  simp [Hzero, wordSum, add_comm]

/-- The lowering lightLight inventory cell equals its named physical band family.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem family_minus_lightLight (u : Fin n → Fin d → ℝ) :
    family m u .minus .lightLight = Lminus m u := by
  rw [family, show wordsIn .minus .lightLight = {(.pDown, .pDown)} by decide]
  simp [Lminus, wordSum]

/-- The lowering lightHeavy inventory cell equals its named physical band family.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem family_minus_lightHeavy (u : Fin n → Fin d → ℝ) :
    family m u .minus .lightHeavy = XplusAdj m u + YplusAdj m u := by
  rw [family, show wordsIn .minus .lightHeavy =
    {(.rDown, .pDown), (.pDown, .rDown)} by decide]
  simp [XplusAdj, YplusAdj, wordSum, add_comm]

/-- The lowering heavyHeavy inventory cell equals its named physical band family.
Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem family_minus_heavyHeavy (u : Fin n → Fin d → ℝ) :
    family m u .minus .heavyHeavy = Hminus m u := by
  rw [family, show wordsIn .minus .heavyHeavy = {(.rDown, .rDown)} by decide]
  simp [Hminus, wordSum]

/-- The paper's displayed `+2` inventory formula.

Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem band_plus_named (u : Fin n → Fin d → ℝ) (ρ : ℝ) :
    band m u ρ .plus =
      Lplus m u + ρ • (Xplus m u + Yplus m u) + ρ ^ 2 • Hplus m u := by
  rw [band_eq_three_families, family_plus_lightLight,
    family_plus_lightHeavy, family_plus_heavyHeavy]

/-- The paper's displayed grade-zero inventory formula.

Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem band_zero_named (u : Fin n → Fin d → ℝ) (ρ : ℝ) :
    band m u ρ .zero = Lzero m u +
      ρ • (Xzero m u + XzeroAdj m u + Yzero m u + YzeroAdj m u) +
      ρ ^ 2 • Hzero m u := by
  rw [band_eq_three_families, family_zero_lightLight,
    family_zero_lightHeavy, family_zero_heavyHeavy]

/-- The paper's displayed `-2` inventory formula.

Source: ported from `SparseFockFormal.NamedBands`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem band_minus_named (u : Fin n → Fin d → ℝ) (ρ : ℝ) :
    band m u ρ .minus =
      Lminus m u + ρ • (XplusAdj m u + YplusAdj m u) +
        ρ ^ 2 • Hminus m u := by
  rw [band_eq_three_families, family_minus_lightLight,
    family_minus_lightHeavy, family_minus_heavyHeavy]

end

end NLAlib.SparseFock.NamedBands
