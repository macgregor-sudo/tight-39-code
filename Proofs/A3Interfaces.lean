module

public import A3Core
public import A3Averaging
public import A3GaugeInvariance
public import NativeRightSU3Action
public import NativeExactCKMConfiguration
public import OriginalFAnalyticDerivativeV2
public import TransportT1
public import TransportT2
public import TransportT3

@[expose] public section
set_option backward.proofsInPublic true

/-!
# A3 interfaces: definitions shared by all pieces

Definitions shared by the first-order calculations; their properties are proved in the importing modules.

* `literalPoint ξ`: MASTER §6.3's literal labelled family at arbitrary phases `ξ = (A,B,C,D)`, with the
  same branches and point order as the seed `ExactCKMConfiguration.nativePoint` (`exactPhases ↦ ξ`).
* `tangentSpace ξ`: the kernel of the real Fréchet derivative of the accepted `originalF` (all 2184
  original rows, all 1053 real coordinates) at `literalCfg ξ`.
* `compensated g π`: the pointwise automorphism `g` combined with the label permutation `π`.
* `R0`, `R1`: the two order-three generators (MASTER §6.5); `R1 := T₁ ∘ R0 ∘ T₁⁻¹`.
* `stdAnchored q W`: the standard anchored Tits form (quartet in frames 0–3, hidden frames 4–12 are
  `p(ω^t W_l)`), with its generator shift `stdShift` and elimination map `elimForward`.
* `AnchorBinding`: everything one anchor must supply.
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial NativePolynomial.ConfigurationResiduals ConfigurationResidualIndices
open CompactAlbert UnitaryErrorBases.ComplexQuartet

/-- Unit complex phases. -/
def IsUnitPhase (ξ : Fin 4 → ℂ) : Prop := ∀ a, Complex.normSq (ξ a) = 1

/-! ## The literal family (MASTER §6.3) -/

/-- Native labelled family at phases `ξ = (A,B,C,D)`; `s` names the frame within group `q`, `t` the outcome. -/
def literalFamilyPoint (ξ : Fin 4 → ℂ) (q : Fin 4) (s t : PhaseIndex) : Glennie.Albert :=
  if q = 0 then literalNativePhasePoint s t
  else if q = 1 then
    nativeOuterProductThird
      (Glennie.octMul (complexOctonion (UnitaryErrorBases.ThreeCycleFourier.character t))
        (nativeOctonionBasis 2))
      (Glennie.octMul (complexOctonion (UnitaryErrorBases.ThreeCycleFourier.character (s + t)))
        (nativeOctonionBasis 4))
  else if q = 2 then
    nativeOuterProductThird
      (Glennie.octMul (complexOctonion (ξ 0 * UnitaryErrorBases.ThreeCycleFourier.character t))
        (nativeOctonionBasis 4))
      (Glennie.octMul (complexOctonion (ξ 1 * UnitaryErrorBases.ThreeCycleFourier.character (s + t)))
        (nativeOctonionBasis 6))
  else
    nativeOuterProductThird
      (Glennie.octMul (complexOctonion (ξ 2 * UnitaryErrorBases.ThreeCycleFourier.character t))
        (nativeOctonionBasis 6))
      (Glennie.octMul (complexOctonion (ξ 3 * UnitaryErrorBases.ThreeCycleFourier.character (s + t)))
        (nativeOctonionBasis 2))

/-- Original frame-grouped point order: coordinate idempotents 0..2, then `3 + 9q + 3s + t`. -/
def literalPoint (ξ : Fin 4 → ℂ) (i : Fin 39) : Glennie.Albert :=
  if hi : i.val < 3 then literalNativeCoordinatePoint ⟨i.val, hi⟩
  else
    let q : Fin 4 := ⟨(i.val - 3) / 9, by have hi39 := i.isLt; omega⟩
    let s : PhaseIndex := (((i.val - 3) % 9) / 3 : ℕ)
    let t : PhaseIndex := ((i.val - 3) % 3 : ℕ)
    literalFamilyPoint ξ q s t

/-- The literal configuration in the original 39 × 27 real coordinates. -/
def literalCfg (ξ : Fin 4 → ℂ) : PartialAction.Configuration ℝ :=
  fun i => upperCoordinates (literalPoint ξ i)

/-- The full real first-order tangent space: kernel of the Fréchet derivative of all 2184 original
residual rows in all 1053 real coordinates, at the literal configuration. -/
def tangentSpace (ξ : Fin 4 → ℂ) : Submodule ℝ (PartialAction.Configuration ℝ) :=
  LinearMap.ker (fderiv ℝ Option2.NativeStress.AnalyticDerivative.originalF (literalCfg ξ)).toLinearMap

/-! ## Labels, compensated actions and native automorphisms -/

/-- The point relabelling `(f, a) ↦ (fperm f, τ f a)` in the original order `3f + a`. -/
def pointRelabel (fperm : Equiv.Perm (Fin 13)) (τ : Fin 13 → Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 39) :=
  (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39).symm.trans
    ((Equiv.prodShear fperm τ).trans (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39))

/-- Outcome shift within every frame: `(f, a) ↦ (f, a + σ f)`. -/
def outcomeShift (σ : Fin 13 → Fin 3) : Equiv.Perm (Fin 39) :=
  pointRelabel (Equiv.refl _) (fun f => Equiv.addRight (σ f))

/-- The compensated action `δ ↦ (i ↦ g (δ (π i)))`. -/
def compensated (g : Glennie.Albert →ₗ[ℝ] Glennie.Albert) (π : Equiv.Perm (Fin 39)) :
    Module.End ℝ (Fin 39 → Glennie.Albert) :=
  LinearMap.pi fun i => g.comp (LinearMap.proj (π i))

/-- A native Jordan automorphism: real-linear, product and trace preserving. -/
structure IsNativeAut (g : Glennie.Albert →ₗ[ℝ] Glennie.Albert) : Prop where
  jordan : ∀ x y, g (Glennie.jordan x y) = Glennie.jordan (g x) (g y)
  trace : ∀ x, Glennie.trace (g x) = Glennie.trace x

/-- The native map of a signed coordinate permutation `(T x)[k] = sgn k * x[perm k]`. -/
def signedTransport (perm : Fin 27 → Fin 27) (sgn : Fin 27 → ℤ) : Glennie.Albert →ₗ[ℝ] Glennie.Albert :=
  upperCoordinateEquiv.symm.toLinearMap ∘ₗ
    (LinearMap.pi fun k => ((sgn k : ℝ)) • LinearMap.proj (perm k)) ∘ₗ upperCoordinateEquiv.toLinearMap

/-- The accepted signed transports `T₁, T₂, T₃` (index `0, 1, 2`), as native maps. -/
def transportT : Fin 3 → Glennie.Albert →ₗ[ℝ] Glennie.Albert
  | 0 => signedTransport TitsS.Transport.T1p TitsS.Transport.T1s
  | 1 => signedTransport TitsS.Transport.T2p TitsS.Transport.T2s
  | 2 => signedTransport TitsS.Transport.T3p TitsS.Transport.T3s

/-- The accepted inverse transport data `T₁⁻¹, T₂⁻¹, T₃⁻¹`, as native maps. -/
def transportTinv : Fin 3 → Glennie.Albert →ₗ[ℝ] Glennie.Albert
  | 0 => signedTransport TitsS.Transport.T1pinv TitsS.Transport.T1si
  | 1 => signedTransport TitsS.Transport.T2pinv TitsS.Transport.T2si
  | 2 => signedTransport TitsS.Transport.T3pinv TitsS.Transport.T3si

/-- First generator: `(a, B) ↦ (a, ω B)` in Tits coordinates (right multiplication by `ω I`). -/
def R0 : Glennie.Albert →ₗ[ℝ] Glennie.Albert :=
  nativeRightMultiply (UnitaryErrorBases.ThreeCycleFourier.omega • (1 : TitsComplexMatrix))

/-- Second generator `R₁ = T₁ R₀ T₁⁻¹` (MASTER §6.5). -/
def R1 : Glennie.Albert →ₗ[ℝ] Glennie.Albert := transportT 0 ∘ₗ R0 ∘ₗ transportTinv 0

/-- The generators of the four order-three subgroups `(1,0), (0,1), (2,2), (2,1)` of `K = C₃ × C₃`. -/
def anchorGenerator : Fin 4 → Module.End ℝ Glennie.Albert
  | 0 => R0
  | 1 => R1
  | 2 => R0 ^ 2 * R1 ^ 2
  | 3 => R0 ^ 2 * R1

/-- Outcome shift compensating `R0` on the literal family (frames 4–12 shift by one). -/
def shift0 (f : Fin 13) : Fin 3 := if f.val < 4 then 0 else 1

/-- Outcome shift compensating `R1`: frames 1–3 by one, 7–9 by two, 10–12 by one. -/
def shift1 (f : Fin 13) : Fin 3 :=
  if f.val = 0 then 0 else if f.val < 4 then 1 else if f.val < 7 then 0 else if f.val < 10 then 2 else 1

/-- The compensating shifts of the four generators. -/
def anchorShift : Fin 4 → Fin 13 → Fin 3
  | 0 => shift0
  | 1 => shift1
  | 2 => fun f => 2 * shift0 f + 2 * shift1 f
  | 3 => fun f => 2 * shift0 f + shift1 f

/-! ## The standard anchored Tits form -/

/-- Hidden-frame labels: frame `4 + k`, with `k = finProdFinEquiv l`. -/
def hiddenFrameEquiv : UnitaryErrorBases.Label ≃ Fin 9 :=
  (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9)

/-- The frame index of hidden label `l`. -/
def hiddenFrame (l : UnitaryErrorBases.Label) : Fin 13 :=
  ⟨4 + (hiddenFrameEquiv l).val, by have := (hiddenFrameEquiv l).isLt; omega⟩

/-- Standard anchored configuration: quartet `q` in frames 0–3 (hidden part zero); hidden frame
`hiddenFrame l` has outcomes `p(ω^t W l)`. -/
def stdAnchored (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (i : Fin 39) : Glennie.Albert :=
  if h : i.val < 12 then
    includeHermitianMatrix (q ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩)
  else
    nativeComplementaryPoint
      ((UnitaryErrorBases.ThreeCycleFourier.omega ^ (i.val % 3)) •
        W (hiddenFrameEquiv.symm ⟨i.val / 3 - 4, by have := i.isLt; omega⟩))

/-- The compensating shift of `R0` on `stdAnchored`: hidden outcomes `t ↦ t + 2`. -/
def stdShift : Equiv.Perm (Fin 39) := outcomeShift (fun f => if f.val < 4 then 0 else 2)

/-- The elimination map: visible parts at the twelve quartet points and three times the hidden part
at outcome 0 of each hidden frame. -/
def elimForward :
    (Fin 39 → Glennie.Albert) →ₗ[ℝ] (Fin 4 → Fin 3 → TitsComplexMatrix) × UnitaryErrorBases.Family :=
  LinearMap.prod
    (LinearMap.pi fun k : Fin 4 => LinearMap.pi fun t : Fin 3 =>
      (LinearMap.fst ℝ TitsComplexMatrix TitsComplexMatrix) ∘ₗ nativeTitsMatrixPair ∘ₗ
        LinearMap.proj (framePointIndex (Fin.castLE (by omega) k) t))
    (LinearMap.pi fun l : UnitaryErrorBases.Label =>
      (3 : ℝ) • ((LinearMap.snd ℝ TitsComplexMatrix TitsComplexMatrix) ∘ₗ nativeTitsMatrixPair ∘ₗ
        LinearMap.proj (framePointIndex (hiddenFrame l) 0)))

/-- First-order space of a labelled quartet `q` in `H₃(ℂ)` (Jordan product `(xy + yx)/2`, trace form
`Re tr(xy)`), written as the native system restricted to visible variations. -/
def quartetFirstOrder (q : Fin 4 → Fin 3 → TitsComplexMatrix) :
    Submodule ℝ (Fin 4 → Fin 3 → TitsComplexMatrix) where
  carrier := {δ |
    (∀ k t, (δ k t).IsHermitian) ∧
    (∀ k t, q k t * δ k t + δ k t * q k t = δ k t) ∧
    (∀ k (s : Fin 3),
      q k (withinPair s).val.1 * δ k (withinPair s).val.2 +
        δ k (withinPair s).val.2 * q k (withinPair s).val.1 +
        δ k (withinPair s).val.1 * q k (withinPair s).val.2 +
        q k (withinPair s).val.2 * δ k (withinPair s).val.1 = 0) ∧
    (∀ k, ∑ t, δ k t = 0) ∧
    (∀ k k' t t', k ≠ k' → (q k t * δ k' t' + δ k t * q k' t').trace.re = 0)}
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3, hx4, hx5⟩ ⟨hy1, hy2, hy3, hy4, hy5⟩
    refine ⟨fun k t => (hx1 k t).add (hy1 k t), fun k t => ?_, fun k s => ?_, fun k => ?_,
      fun k k' t t' hk => ?_⟩
    · simp only [Pi.add_apply, mul_add, add_mul]
      calc _ = (q k t * x k t + x k t * q k t) + (q k t * y k t + y k t * q k t) := by abel
        _ = _ := by rw [hx2 k t, hy2 k t]
    · simp only [Pi.add_apply, mul_add, add_mul]
      calc _ = (q k (withinPair s).val.1 * x k (withinPair s).val.2 +
              x k (withinPair s).val.2 * q k (withinPair s).val.1 +
              x k (withinPair s).val.1 * q k (withinPair s).val.2 +
              q k (withinPair s).val.2 * x k (withinPair s).val.1) +
            (q k (withinPair s).val.1 * y k (withinPair s).val.2 +
              y k (withinPair s).val.2 * q k (withinPair s).val.1 +
              y k (withinPair s).val.1 * q k (withinPair s).val.2 +
              q k (withinPair s).val.2 * y k (withinPair s).val.1) := by abel
        _ = 0 := by rw [hx3 k s, hy3 k s, add_zero]
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hx4 k, hy4 k, add_zero]
    · simp only [Pi.add_apply, mul_add, add_mul]
      rw [show q k t * x k' t' + q k t * y k' t' + (x k t * q k' t' + y k t * q k' t') =
          (q k t * x k' t' + x k t * q k' t') + (q k t * y k' t' + y k t * q k' t') by abel,
        Matrix.trace_add, Complex.add_re, hx5 k k' t t' hk, hy5 k k' t t' hk, add_zero]
  zero_mem' := by
    refine ⟨fun k t => Matrix.isHermitian_zero, fun k t => ?_, fun k s => ?_, fun k => ?_,
      fun k k' t t' _ => ?_⟩ <;> simp
  smul_mem' := by
    rintro c x ⟨hx1, hx2, hx3, hx4, hx5⟩
    refine ⟨fun k t => ?_, fun k t => ?_, fun k s => ?_, fun k => ?_, fun k k' t t' hk => ?_⟩
    · exact Matrix.IsHermitian.smul (hx1 k t) (IsSelfAdjoint.all c)
    · simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, hx2 k t]
    · simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, hx3 k s, smul_zero]
    · simp only [Pi.smul_apply, ← Finset.smul_sum, hx4 k, smul_zero]
    · simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, Matrix.trace_smul,
        Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        hx5 k k' t t' hk, mul_zero]

/-- The standard complete complex quartet: coordinate projectors, then the nine phase projectors. -/
def stdQuartet : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian}
  | 0, t => ⟨coordinateProjector t, coordinateProjector_isHermitian t⟩
  | ⟨k + 1, _⟩, t => ⟨phaseProjector (k : PhaseIndex) (t : PhaseIndex),
      phaseProjector_isHermitian _ _⟩

/-! ## Phase triples and the per-anchor binding -/

/-- The four normalized phase triples `d_H` of the brief (index `j : ZMod 3`), with `ξ = (A,B,C,D)`. -/
def anchorPhases (ξ : Fin 4 → ℂ) : Fin 4 → UnitaryErrorBases.Index → ℂ := CKM.NativeFirstOrder.selectFour (![ξ 0 * ξ 1 / ξ 2, (ξ 0 * ξ 3)⁻¹, ξ 2 * ξ 3 / ξ 1]) (![ξ 0 * ξ 2 * ξ 3, -(ξ 1 / ξ 2), -(ξ 0 * ξ 1 * ξ 3)⁻¹]) (![-(ξ 2 * ξ 3), (ξ 2)⁻¹, -(ξ 3)⁻¹]) (![-(ξ 0)⁻¹, -(ξ 1)⁻¹, ξ 0 * ξ 1])
/-- Everything one anchor supplies: a native automorphism `Ψ` conjugating the anchor generator `ρ`
to `R0`, a frame/outcome relabelling `λ` compatible with the shifts, and the standard anchored form of
`Ψ ∘ P ∘ λ` with an idempotent quartet of tangent dimension eight and a unitary error basis whose
first-order space has the accepted dimension `18 + 2 r(d)`. -/
structure AnchorBinding (ρ : Module.End ℝ Glennie.Albert) (σ : Fin 13 → Fin 3)
    (P : Fin 39 → Glennie.Albert) (d : UnitaryErrorBases.PhaseTriple) where
  Ψ : Glennie.Albert →ₗ[ℝ] Glennie.Albert
  Ψ_aut : IsNativeAut Ψ
  Ψ_injective : Function.Injective Ψ
  conj : Ψ ∘ₗ ρ = R0 ∘ₗ Ψ
  fperm : Equiv.Perm (Fin 13)
  τ : Fin 13 → Equiv.Perm (Fin 3)
  shift_compat : ∀ i, outcomeShift σ (pointRelabel fperm τ i) = pointRelabel fperm τ (stdShift i)
  q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian}
  q_idem : ∀ k t, (q k t).val * (q k t).val = (q k t).val
  q_finrank : Module.finrank ℝ (quartetFirstOrder fun k t => (q k t).val) = 8
  W : UnitaryErrorBases.Family
  W_ueb : UnitaryErrorBases.IsUnitaryErrorBasis W
  W_finrank : Module.finrank ℝ (UnitaryErrorBases.firstOrderSpace W) =
    18 + 2 * UnitaryErrorBases.resonanceCount d
  form : ∀ i, Ψ (P (pointRelabel fperm τ i)) = stdAnchored q W i

end CKM.NativeFirstOrder
