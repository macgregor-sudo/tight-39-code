module

public import GSMain
public import A4Main
public import A3Main
public import A5SU3
public import A5Chart

@[expose] public section

/-!
# A5 definitions: the four actual fixed-quartet families, the common phase family and their slices
(definitions only)

Notation. `P = literalCfg ξ₀` is A3's literal 39-point configuration (original labels, 1053 real
coordinates), `G = autC` the full native automorphism group and `slicePH` the analytic slice chart of
the group/slice package, `N = normalC ξ₀` (dimension 1001).

**Anchored model (A3's bindings).** For each anchor `H`, A3 proves
`anchorΨ H (literalPoint ξ (anchorRelabel H i)) = stdAnchored q W i` with a signed native transport
`anchorΨ H` (identity or `T⁻¹`), a frame/outcome relabelling, the quartet `q = anchorQuartet ξ H`
(the standard complex quartet conjugated by the diagonal unitary `quartetConj ξ H`) and a unitary
error basis `W` in gauge form `W l = c l • (L * E_(σ l)(d) * R)`, `E = monomialFamily`, `d` the
anchor's phase triple. All these data are explicit functions of `ξ`.

**Raw fixed-quartet family.** `preCfg ξ₀ H g h d` keeps the quartet of anchor `H` fixed and puts
the hidden matrix `c l • (g * L * E_(σ l)(d) * R * hᴴ)` (with `L, R, c, σ` frozen at `ξ₀`) in label
`l`, transported back to the original labels. In the brief's notation this is the eighteen-parameter
model `Ψ(g', h', d) = g' E(d) h'ᴴ` with `g' = g L`, `h' = h Rᴴ`, read at label `σ l` and rephased by
the cube root of unity `c l`; the constants come from A3's binding at `ξ₀`. At `g = h = 1`,
`d = d_H(ξ₀)` it is `P` (`preCfg_base`). `preMap` reads `g, h` through the `SU(3)` chart `suExp`
and `d` through the torus chart `torusPhase`; `rawMap` saturates by `G` through `groupChart`
(52 + 8 + 8 + 2 = 70 parameters); `rawMap62` fixes `h = 1` (the proved complement of the
eight-dimensional kernel).

**Common family.** `commonMap ξ₀ (D, θ) = groupChart D • P(ξ₀ · e^{iθ})` (52 + 4 parameters).

**Slice.** `sliceRep y = ((slicePH).symm y).2 ∈ N` is the slice coordinate; `sliceFam ξ₀ hξ₀ H`
and `sliceCommon ξ₀ hξ₀` are the slice representatives of the families (10 and 4 parameters).

**K action.** `kAct H` is A4's `confGen` of anchor generator `H` with its outcome shift, a linear map
on all of `Cfg`. `tanN = T ∩ N` models `Q = T/O`; `fixQ ξ₀ H = Q^H`, `fixQK ξ₀ = Q^K`.
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix

namespace CKM.NativeFourFamily

/-! ## Phases -/

/-- The explicit good-phase predicate: unit phases and all twelve signed anchor phases have cube `≠ 1`. -/
def IsGoodPhase (ξ : Fin 4 → ℂ) : Prop :=
  IsUnitPhase ξ ∧ ∀ (H : Fin 4) (j : Index), anchorPhases ξ H j ^ 3 ≠ 1

/-- Phase variation `ξ₀ · e^{iθ}`. -/
def commonPhase (ξ₀ : Fin 4 → ℂ) (θ : Fin 4 → ℝ) : Fin 4 → ℂ :=
  fun a => ξ₀ a * Complex.exp ((θ a : ℂ) * Complex.I)

/-- Angles of the phase-triple torus chart (product one). -/
def torusAngles (e : Fin 2 → ℝ) : Index → ℝ := ![e 0, e 1, -(e 0) - e 1]

/-- Torus chart of phase triples at `d₀`: `d j = d₀ j · e^{i ε_j(e)}`. -/
def torusPhase (d₀ : PhaseTriple) (e : Fin 2 → ℝ) : PhaseTriple :=
  ⟨fun j => d₀.val j * Complex.exp ((torusAngles e j : ℂ) * Complex.I), by
    refine ⟨fun j => ?_, ?_⟩
    · rw [map_mul, d₀.2.1 j, one_mul, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I,
        one_pow]
    · rw [Finset.prod_mul_distrib, d₀.2.2, one_mul, ← Complex.exp_sum, ← Finset.sum_mul]
      have : ∑ j : Index, (torusAngles e j : ℂ) = 0 := by
        exact (Fin.sum_univ_three (fun j : Fin 3 => (torusAngles e j : ℂ))).trans
          (by simp [torusAngles])
      rw [this, zero_mul, Complex.exp_zero]⟩

/-! ## Per-anchor data (A3's bindings, as explicit functions of `ξ`) -/

/-- The signed native transport of A3's binding (`Ψ`). -/
def anchorΨ : Fin 4 → Glennie.Albert →ₗ[ℝ] Glennie.Albert
  | 0 => LinearMap.id
  | 1 => transportTinv 0
  | 2 => transportTinv 1
  | 3 => transportTinv 2

/-- Its inverse. -/
def anchorΨinv : Fin 4 → Glennie.Albert →ₗ[ℝ] Glennie.Albert
  | 0 => LinearMap.id
  | 1 => transportT 0
  | 2 => transportT 1
  | 3 => transportT 2

/-- A3's frame/outcome relabelling. -/
def anchorRelabel : Fin 4 → Equiv.Perm (Fin 39)
  | 0 => pointRelabel (Equiv.refl _) Anchor0.anchor0τ
  | 1 => pointRelabel Anchor1.fperm1 Anchor1.tau1
  | 2 => pointRelabel Anchor2.fperm2 Anchor2.τ2
  | 3 => pointRelabel Anchor3.fperm3 Anchor3.τ3

/-- A3's anchored quartet at phase `ξ`. -/
def anchorQuartet (ξ : Fin 4 → ℂ) : Fin 4 → Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian}
  | 0 => stdQuartet
  | 1 => Anchor1.q1
  | 2 => Anchor2.q2 ξ
  | 3 => Anchor3.q3 ξ

/-- The diagonal unitary conjugating the standard quartet to `anchorQuartet ξ H`. -/
def quartetConj (ξ : Fin 4 → ℂ) : Fin 4 → TitsComplexMatrix
  | 0 => 1
  | 1 => Anchor1.gQ
  | 2 => Anchor2.g2 ξ
  | 3 => Anchor3.g3 ξ

/-- Left gauge `L` of A3's gauge form. -/
def gaugeLeft (ξ : Fin 4 → ℂ) : Fin 4 → Mat
  | 0 => Anchor0.gaugeL ξ
  | 1 => Anchor1.asMat (Anchor1.Lg ξ)
  | 2 => Anchor2.gaugeL ξ
  | 3 => Anchor3.gaugeL3

/-- Right gauge `R` of A3's gauge form. -/
def gaugeRight (ξ : Fin 4 → ℂ) : Fin 4 → Mat
  | 0 => Anchor0.gaugeR ξ
  | 1 => Anchor1.asMat (Anchor1.Rg ξ)
  | 2 => Anchor2.gaugeR ξ
  | 3 => 1

/-- Central rephasing `c` (cube roots of unity). -/
def gaugeScalar : Fin 4 → Label → ℂ
  | 0 => Anchor0.gaugeC
  | 1 => fun _ => 1
  | 2 => Anchor2.gaugeC
  | 3 => Anchor3.gaugeC3

/-- Label permutation `σ`. -/
def gaugeLabel : Fin 4 → Label ≃ Label
  | 0 => Anchor0.gaugeσ
  | 1 => Anchor1.sigma1
  | 2 => Equiv.refl _
  | 3 => Anchor3.gaugeσ3

/-! ## The raw fixed-quartet families -/

/-- Hidden matrices `c l • (g * L * E_(σ l)(d) * R * hᴴ)`, gauge frozen at `ξ₀`. -/
def hidFamily (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (g h : Mat) (d : PhaseTriple) : Family :=
  fun l => gaugeScalar H l •
    (g * gaugeLeft ξ₀ H * monomialFamily d (gaugeLabel H l) * gaugeRight ξ₀ H * hᴴ)

/-- Native points of the raw family, in the original labels. -/
def prePoint (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (g h : Mat) (d : PhaseTriple) (i : Fin 39) :
    Glennie.Albert :=
  anchorΨinv H (stdAnchored (anchorQuartet ξ₀ H) (hidFamily ξ₀ H g h d) ((anchorRelabel H).symm i))

/-- The raw family in the original 1053 coordinates. -/
def preCfg (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (g h : Mat) (d : PhaseTriple) : Cfg :=
  fun i => NativePolynomial.upperCoordinates (prePoint ξ₀ H g h d i)

/-- Parameters `(X, Y, e)`: `g = suExp X`, `h = suExp Y`, `d = torusPhase d_H(ξ₀) e`. -/
abbrev PreParam := (Fin 8 → ℝ) × (Fin 8 → ℝ) × (Fin 2 → ℝ)

/-- The eighteen-parameter pre-saturation family in charts. -/
def preMap (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : PreParam) : Cfg :=
  preCfg ξ₀ H (suExp p.1) (suExp p.2.1) (torusPhase (anchorTriple ξ₀ hξ₀ H) p.2.2)

/-- Parameters of the `G`-saturated family: `52 + 18 = 70`. -/
abbrev RawParam := ↥derC × PreParam

/-- The `G`-saturated raw family. -/
def rawMap (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : RawParam) : Cfg :=
  actC (groupChart p.1) (preMap ξ₀ hξ₀ H p.2)

/-- Parameters of the complement `h = 1`: `52 + 8 + 2 = 62`. -/
abbrev RawParam62 := ↥derC × (Fin 8 → ℝ) × (Fin 2 → ℝ)

/-- The raw family on the complement `h = 1` of the right-gauge kernel. -/
def rawMap62 (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : RawParam62) : Cfg :=
  rawMap ξ₀ hξ₀ H (p.1, p.2.1, 0, p.2.2)

/-- Parameters of the common family: `52 + 4 = 56`. -/
abbrev CommonParam := ↥derC × (Fin 4 → ℝ)

/-- The `G`-saturation of the literal four-phase family. -/
def commonMap (ξ₀ : Fin 4 → ℂ) (p : CommonParam) : Cfg :=
  actC (groupChart p.1) (literalCfg (commonPhase ξ₀ p.2))

/-! ## Derivatives -/

/-- Linear part of the hidden point map `U ↦ p(U) = (I/3, U/3)`. -/
def hiddenVec (U : TitsComplexMatrix) : Glennie.Albert :=
  Elim.mkPoint 0 Matrix.isHermitian_zero ((1 / 3 : ℂ) • U)

/-- First-order variation of `stdAnchored q W` when `W` moves by `V` (the quartet does not move). -/
def stdAnchoredVar (V : Family) (i : Fin 39) : Glennie.Albert :=
  if h : i.val < 12 then 0
  else hiddenVec ((UnitaryErrorBases.ThreeCycleFourier.omega ^ (i.val % 3)) •
    V (hiddenFrameEquiv.symm ⟨i.val / 3 - 4, by omega⟩))

/-- Derivative of `monomialFamily` in the phase triple, in direction `δ`. -/
def monomialVar (δ : Index → ℂ) : Family :=
  fun p => shift ^ p.2.val * (if p.2 = 2 then Matrix.diagonal δ else 0) * clock ^ p.1.val

/-- Derivative of `torusPhase d₀` at `0` in direction `e`. -/
def torusVar (d₀ : PhaseTriple) (e : Fin 2 → ℝ) : Index → ℂ :=
  fun j => d₀.val j * ((torusAngles e j : ℂ) * Complex.I)

/-- Derivative of the hidden family at `(1, 1, d₀)` in direction `(X, Y, δ)`. -/
def hidVar (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (d₀ : PhaseTriple) (X Y : Mat) (δ : Index → ℂ) : Family :=
  fun l => gaugeScalar H l •
    (X * gaugeLeft ξ₀ H * monomialFamily d₀ (gaugeLabel H l) * gaugeRight ξ₀ H +
      gaugeLeft ξ₀ H * monomialFamily d₀ (gaugeLabel H l) * gaugeRight ξ₀ H * Yᴴ +
      gaugeLeft ξ₀ H * monomialVar δ (gaugeLabel H l) * gaugeRight ξ₀ H)

/-- The explicit derivative of `preMap` at `0`. -/
def preVar (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : PreParam) : Cfg :=
  fun i => NativePolynomial.upperCoordinates (anchorΨinv H (stdAnchoredVar
    (hidVar ξ₀ H (anchorTriple ξ₀ hξ₀ H) (suMat p.1) (suMat p.2.1)
      (torusVar (anchorTriple ξ₀ hξ₀ H) p.2.2)) ((anchorRelabel H).symm i)))

/-- Strict derivatives at `0` (equal to explicit formulas by `preDer_apply`, `rawDer_apply`). -/
def preDer (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) : PreParam →L[ℝ] Cfg :=
  fderiv ℝ (preMap ξ₀ hξ₀ H) 0

def rawDer (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) : RawParam →L[ℝ] Cfg :=
  fderiv ℝ (rawMap ξ₀ hξ₀ H) 0

def rawDer62 (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) : RawParam62 →L[ℝ] Cfg :=
  fderiv ℝ (rawMap62 ξ₀ hξ₀ H) 0

/-- Derivative of the literal phase family at `θ = 0`. -/
def phaseDer (ξ₀ : Fin 4 → ℂ) : (Fin 4 → ℝ) →L[ℝ] Cfg :=
  fderiv ℝ (fun θ => literalCfg (commonPhase ξ₀ θ)) 0

def commonDer (ξ₀ : Fin 4 → ℂ) : CommonParam →L[ℝ] Cfg :=
  fderiv ℝ (commonMap ξ₀) 0

/-! ## The right gauge and the quartet fixer -/

/-- Infinitesimal right multiplication `(a, B) ↦ (0, B Z)`. -/
def rightDer (Z : TitsComplexMatrix) : Module.End ℝ Glennie.Albert :=
  nativeRightMultiply Z - nativeRightMultiply 0

/-- The right gauge of anchor `H`, transported to the original frame, in coordinates. -/
def gaugeDer (H : Fin 4) (k : Fin 8 → ℝ) : CEnd :=
  coordEnd (anchorΨinv H ∘ₗ rightDer (suMat k) ∘ₗ anchorΨ H)

/-- Original labels of the twelve quartet points of anchor `H`. -/
def quartetLabel (H : Fin 4) (j : Fin 12) : Fin 39 :=
  anchorRelabel H ⟨j.val, by omega⟩

/-- Derivations (in coordinates) vanishing on the twelve quartet points of anchor `H` at `P`. -/
def quartetFixer (ξ₀ : Fin 4 → ℂ) (H : Fin 4) : Submodule ℝ CEnd :=
  derC ⊓ ⨅ j : Fin 12, LinearMap.ker
    (ContinuousLinearMap.apply ℝ Coord (literalCfg ξ₀ (quartetLabel H j))).toLinearMap

/-! ## Slices -/

/-- The slice coordinate of `y` (its `normalC` component in the group/slice chart). -/
def sliceRep (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (y : Cfg) : ↥(normalC ξ₀) :=
  ((slicePH ξ₀ hξ₀).symm y).2

abbrev SliceParam := (Fin 8 → ℝ) × (Fin 2 → ℝ)

/-- The ten-parameter slice family of anchor `H`. -/
def sliceFam (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : SliceParam) : ↥(normalC ξ₀) :=
  sliceRep ξ₀ hξ₀ (preMap ξ₀ hξ₀ H (p.1, 0, p.2))

/-- The four-parameter common slice family. -/
def sliceCommon (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (θ : Fin 4 → ℝ) : ↥(normalC ξ₀) :=
  sliceRep ξ₀ hξ₀ (literalCfg (commonPhase ξ₀ θ))

def sliceFamDer (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) : SliceParam →L[ℝ] ↥(normalC ξ₀) :=
  fderiv ℝ (sliceFam ξ₀ hξ₀ H) 0

def sliceCommonDer (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) : (Fin 4 → ℝ) →L[ℝ] ↥(normalC ξ₀) :=
  fderiv ℝ (sliceCommon ξ₀ hξ₀) 0

/-! ## The compensated `K = C₃ × C₃` action -/

/-- The compensated anchor generator `H`, on all of `Cfg` (A4's `confGen`). -/
def kAct (H : Fin 4) : Module.End ℝ Cfg :=
  CKM.NativeIntrinsicTriality.confGen (anchorGenerator H) (anchorShift H)

/-- Its effect on group elements: `A ↦ ρ A ρ²`. -/
def kConj (H : Fin 4) (A : CEnd) : CEnd :=
  coordEnd (anchorGenerator H) * A * coordEnd (anchorGenerator H ^ 2)

/-- `Q = T ∩ N`, a `K`-stable complement of `O` in `T`. -/
def tanN (ξ₀ : Fin 4 → ℂ) : Submodule ℝ Cfg := tangentSpace ξ₀ ⊓ normalC ξ₀

/-- `Q^H`. -/
def fixQ (ξ₀ : Fin 4 → ℂ) (H : Fin 4) : Submodule ℝ Cfg := tanN ξ₀ ⊓ fixedSpace (kAct H)

/-- `Q^K`. -/
def fixQK (ξ₀ : Fin 4 → ℂ) : Submodule ℝ Cfg :=
  tanN ξ₀ ⊓ fixedSpace (kAct 0) ⊓ fixedSpace (kAct 1)

/-! ## Chart models -/

/-- `ℝ⁴ × (ℝ⁶)⁴ × ℝ⁹⁷³` (slice, `4 + 24 + 973 = 1001`). -/
abbrev SliceModel := (Fin 4 → ℝ) × (Fin 4 → Fin 6 → ℝ) × (Fin 973 → ℝ)

/-- `ℝ⁵⁶ × (ℝ⁶)⁴ × ℝ⁹⁷³` (raw, `56 + 24 + 973 = 1053`). -/
abbrev RawModel := (Fin 56 → ℝ) × (Fin 4 → Fin 6 → ℝ) × (Fin 973 → ℝ)

end CKM.NativeFourFamily
