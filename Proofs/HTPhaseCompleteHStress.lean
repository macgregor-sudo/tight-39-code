module

public import HTPhaseCompleteCartan
public import NativeHFixedBaseConsumer

@[expose] public section

/-!
# Transported H covectors: equilibrium at EVERY unit phase (first-party)

1. Row covariance: for a native automorphism `g` (`TitsS.IsAut`) applied to every state,
   `F(g·C) = ρ_g F(C)`, with `ρ_g` acting by `g` on each idempotency and frame-sum 27-block and as the
   identity on the trace and pair rows.
2. The transported weights `ellRaw ξ i a := weightC i a ∘ ρ_E`, `E = d_i(U)⁻¹ = d_i(U⁻¹)`,
   `U = ξ / exactPhases`: `Σ_r ellRaw_r y_r = Σ_q weightC_q (ρ_E y)_q` (`ellRaw_contract`).
3. Equilibrium for every unit `ξ` (resonant included): the accepted fixed-base equilibrium
   `book_h_equilibrium`, the accepted anchor support `hasAnchorSupport` and the accepted quadratic line
   identity `contractedF_line_eq_quadratic_at_anchor`, applied after the covariance, with the anchor
   matching `cartan_inv_anchor` (12 quartet states only) and the accepted literal bridge `phi_bridge`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Option2.NativeStress.HTPhaseComplete

open scoped BigOperators
open MvPolynomial PolynomialJets
open TitsS (IsAut)
open NativePolynomial NativePolynomial.PartialAction NativePolynomial.CoordinateMaps
open NativePolynomial.ConfigurationResiduals ConfigurationResidualIndices
open Option2.NativeStress.AnchorSupport Option2.NativeStress.HTPhaseKron
open CKM.NativeFirstOrder QuadraticCertificate.ExactCKMConfiguration

/-! ## 1. Row covariance -/

/-- The literal block action of a native vector map on typed residual values. -/
def labelAct (g : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ)) (y : FLabel → ℂ) : FLabel → ℂ
  | .inl (i, k) => g (fun j => y (fId i j)) k
  | .inr (.inl i) => y (fTrace i)
  | .inr (.inr (.inl (f, k))) => g (fun j => y (fSum f j)) k
  | .inr (.inr (.inr ij)) => y (fPair ij)

theorem originalValue_cov (g : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ)) (hg : IsAut (1 / 2 : ℂ) g)
    (C : Configuration ℂ) (q : FLabel) :
    originalValue (1 / 2 : ℂ) (1 / 3 : ℂ) (fun i => g (C i)) q =
      labelAct g (originalValue (1 / 2 : ℂ) (1 / 3 : ℂ) C) q := by
  rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · change coordinateProduct (1 / 2 : ℂ) (g (C i)) (g (C i)) k - g (C i) k =
      g (coordinateProduct (1 / 2 : ℂ) (C i) (C i) - C i) k
    rw [← hg.map_prod, map_sub]
    rfl
  · change coordinateTrace (g (C i)) - 1 = coordinateTrace (C i) - 1
    rw [hg.map_trace]
  · change (∑ a : Fin 3, g (C (framePointIndex f a)) k) - coordinateUnit k =
      g (fun j => (∑ a : Fin 3, C (framePointIndex f a) j) - coordinateUnit j) k
    have hv : (∑ a : Fin 3, g (C (framePointIndex f a))) - coordinateUnit =
        g ((∑ a : Fin 3, C (framePointIndex f a)) - coordinateUnit) := by
      rw [map_sub, map_sum, hg.map_unit]
    have hvec : (∑ a : Fin 3, C (framePointIndex f a)) - coordinateUnit =
        (fun j => (∑ a : Fin 3, C (framePointIndex f a) j) - coordinateUnit j) := by
      funext j
      simp only [Finset.sum_apply, Pi.sub_apply]
    rw [hvec] at hv
    simpa only [Finset.sum_apply, Pi.sub_apply] using congrFun hv k
  · change coordinatePairing (g (C ij.val.1)) (g (C ij.val.2)) - _ =
      coordinatePairing (C ij.val.1) (C ij.val.2) - _
    rw [hg.map_pairing]

/-- The row action on numbered residual vectors, as a complex-linear map. -/
def rowAct (g : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ)) : (Fin 2184 → ℂ) →ₗ[ℂ] (Fin 2184 → ℂ) where
  toFun y r := labelAct g (fun q => y (fNumber q)) (fNumber.symm r)
  map_add' y z := by
    funext r
    simp only [Pi.add_apply]
    rcases fNumber.symm r with ⟨i, k⟩ | i | ⟨f, k⟩ | ij <;> simp only [labelAct]
    · rw [show (fun j => y (fNumber (fId i j)) + z (fNumber (fId i j))) =
        (fun j => y (fNumber (fId i j))) + (fun j => z (fNumber (fId i j))) from rfl, map_add]; rfl
    · rw [show (fun j => y (fNumber (fSum f j)) + z (fNumber (fSum f j))) =
        (fun j => y (fNumber (fSum f j))) + (fun j => z (fNumber (fSum f j))) from rfl, map_add]; rfl
  map_smul' c y := by
    funext r
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rcases fNumber.symm r with ⟨i, k⟩ | i | ⟨f, k⟩ | ij <;> simp only [labelAct]
    · rw [show (fun j => c * y (fNumber (fId i j))) = c • (fun j => y (fNumber (fId i j))) from rfl,
        map_smul]; rfl
    · rw [show (fun j => c * y (fNumber (fSum f j))) = c • (fun j => y (fNumber (fSum f j))) from rfl,
        map_smul]; rfl

/-- Ambient vector to configuration (inverse of `pack`). -/
def unpackC (X : Fin 1053 → ℂ) : Configuration ℂ := fun i k => X ⟨27 * i.val + k.val, by omega⟩

theorem pack_unpackC (X : Fin 1053 → ℂ) : pack (unpackC X) = X := by
  funext v
  simp only [pack, unpackC]
  congr 1
  ext
  simp only
  omega

/-- A native vector map applied to every one of the 39 states. -/
def stateAct (g : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ)) (X : Fin 1053 → ℂ) : Fin 1053 → ℂ :=
  pack (fun i => g (unpackC X i))

theorem stateAct_add (g : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ)) (X Y : Fin 1053 → ℂ) (t : ℂ) :
    stateAct g (X + t • Y) = stateAct g X + t • stateAct g Y := by
  funext v
  simp only [stateAct, pack, Pi.add_apply, Pi.smul_apply]
  have : unpackC (X + t • Y) ⟨v.val / 27, by omega⟩ =
      unpackC X ⟨v.val / 27, by omega⟩ + t • unpackC Y ⟨v.val / 27, by omega⟩ := by
    funext k; simp [unpackC]
  rw [this, map_add, map_smul]
  rfl

/-- **Row covariance** on the original numbered complex rows, every configuration (no solution
premise). -/
theorem row_covariance (g : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ)) (hg : IsAut (1 / 2 : ℂ) g)
    (X : Fin 1053 → ℂ) (r : Fin 2184) :
    eval (stateAct g X) (row r) = rowAct g (fun q => eval X (row q)) r := by
  unfold stateAct row
  rw [eval_fRow, originalValue_cov g hg]
  change labelAct g (originalValue (1 / 2 : ℂ) (1 / 3 : ℂ) (unpackC X)) (fNumber.symm r) =
    labelAct g (fun q => eval X (fRow (1 / 2 : ℂ) (1 / 3 : ℂ) (fNumber q))) (fNumber.symm r)
  congr 1
  funext q
  rw [← pack_unpackC X, eval_fRow, Equiv.symm_apply_apply, pack_unpackC]

/-! ## 2. Transported weights -/

/-- `E = d_i(U)⁻¹` as a complex-linear native map. -/
noncomputable def invCartan (U : Fin 4 → ℂˣ) (i : Fin 4) : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ) :=
  cartanLin (Uinv U) i

theorem invCartan_isAut (U : Fin 4 → ℂˣ) (i : Fin 4) : IsAut (1 / 2 : ℂ) (invCartan U i) :=
  cartan_isAut (Uinv U) i

/-- Explicit transported weight: row `r` of `ℓ ∘ ρ_E`. On trace and pair rows it equals `ℓ`; on an
idempotency/frame-sum row `(blk, m)` it is `Σ_n ℓ(blk, n) E[n, m]`. -/
noncomputable def ellRawU (U : Fin 4 → ℂˣ) (i : Fin 4) (a : Fin 3) : Weights := fun r =>
  ∑ q : Fin 2184, NativeH.weightC i a q * rowAct (invCartan U i) (Pi.single r 1) q

theorem ellRaw_contract (U : Fin 4 → ℂˣ) (i : Fin 4) (a : Fin 3) (y : Fin 2184 → ℂ) :
    ∑ r : Fin 2184, ellRawU U i a r * y r =
      ∑ q : Fin 2184, NativeH.weightC i a q * rowAct (invCartan U i) y q := by
  have hy : y = ∑ r : Fin 2184, y r • (Pi.single r (1 : ℂ) : Fin 2184 → ℂ) := by
    funext q; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hy]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ellRawU,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ => by ring

/-- Contracted original F transports: `ℓ_t · F(X) = ℓ · F(E · X)` for every complex ambient `X`. -/
theorem contractedF_transport (U : Fin 4 → ℂˣ) (i : Fin 4) (a : Fin 3) (X : Fin 1053 → ℂ) :
    contractedF (ellRawU U i a) X = contractedF (NativeH.weightC i a) (stateAct (invCartan U i) X) := by
  unfold contractedF
  rw [ellRaw_contract]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [row_covariance _ (invCartan_isAut U i)]

/-! ## 3. Equilibrium at every unit phase -/

/-- The phase units `U = ξ / exactPhases`. -/
noncomputable abbrev Ux (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Fin 4 → ℂˣ := Uph ξ hξ

/-- Transported (not yet character-normalised) H weights at phase `ξ`. -/
noncomputable def ellRaw (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3) : Weights :=
  ellRawU (Ux ξ hξ) i a

/-- The accepted base point, complexified. -/
noncomputable def Pbase : Ambient := fun v => ((pack (literalCfg exactPhases) v : ℝ) : ℂ)

theorem eval_real_row (x : Fin 1053 → ℝ) (r : Fin 2184) :
    eval (fun v => ((x v : ℝ) : ℂ)) (row r) = ((Option2.NativeStress.originalF x r : ℝ) : ℂ) := by
  have hrow : MvPolynomial.map Complex.ofRealHom
      (NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r) = row r := by
    simpa [row] using FourSheets.PointBridge.Rows.map_fRow
      Complex.ofRealHom (1 / 2 : ℝ) (1 / 3 : ℝ) r
  rw [← hrow, eval_map]
  exact (eval₂_comp Complex.ofRealHom x
    (NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r)).symm

theorem Pbase_solution (r : Fin 2184) : eval Pbase (row r) = 0 := by
  have h := (originalEquations_iff_all_fRows _ _ _).mp seed_originalEquations r
  unfold Pbase
  rw [eval_real_row]
  simp only [Option2.NativeStress.originalF, h, Complex.ofReal_zero]

theorem Pbase_eq_bookBase : Pbase = fun v => ((Option2.BookNativeBase.bookBase v : ℝ) : ℂ) := by
  funext v
  simp only [Pbase, pack_literalCfg_exactPhases, Option2.BookNativeBase.bookBase_eq_pointCoordinates]

theorem Pbase_equilibrium (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    ∑ r : Fin 2184, NativeH.weightC i a r * equationLinearMatrix (translatedRow Pbase) r c = 0 := by
  rw [Pbase_eq_bookBase]
  exact NativeH.Equilibrium.book_h_equilibrium i a c

theorem anchor_quartet (i : Fin 4) (v : Fin 1053) (hv : AnchorCoordinate i v) :
    quartetState i (v.val / 27) = true := by
  unfold AnchorCoordinate at hv
  have : v.val / 81 = v.val / 27 / 3 := by omega
  simp only [quartetState, decide_eq_true_eq]
  omega

/-- **Anchor agreement used by the transport**: `E · Pξ = P_base` on the anchors of quartet `i`. -/
theorem transported_anchor (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (v : Fin 1053)
    (hv : AnchorCoordinate i v) :
    stateAct (invCartan (Ux ξ hξ) i) (fun w => ((pack (literalCfg ξ) w : ℝ) : ℂ)) v = Pbase v := by
  have hq := anchor_quartet i v hv
  have hk : v.val / 27 < 39 := by omega
  have hX : unpackC (fun w => ((pack (literalCfg ξ) w : ℝ) : ℂ)) ⟨v.val / 27, hk⟩ =
      fun c => PhiR Q12.toComplex (Uph ξ hξ) ⟨27 * (v.val / 27) + c.val, by omega⟩ := by
    funext c
    simp only [unpackC]
    rw [phi_bridge]
  change (invCartan (Ux ξ hξ) i) (unpackC (fun w => ((pack (literalCfg ξ) w : ℝ) : ℂ))
    ⟨v.val / 27, hk⟩) ⟨v.val % 27, Nat.mod_lt _ (by norm_num)⟩ = Pbase v
  rw [hX]
  rw [show (⇑(invCartan (Ux ξ hξ) i) : (Fin 27 → ℂ) → (Fin 27 → ℂ)) =
    cartanFun (Uinv (Uph ξ hξ)) i from rfl]
  rw [cartan_inv_anchor (Uph ξ hξ) i (v.val / 27) hk hq]
  simp only [bvec, Pbase]
  rw [base_link]
  unfold Cn
  have e : 27 * (v.val / 27) + v.val % 27 = v.val := Nat.div_add_mod _ _
  rw [dif_pos (by omega)]
  congr 3

/-- The quadratic line identity for the transported weights at every unit phase, every real line. -/
theorem transported_line (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3)
    (W : Fin 1053 → ℝ) (t : ℝ) :
    AnalyticDerivative.stressCovector (ellRaw ξ hξ i a)
        (Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ) + t • W)) =
      (t : ℂ) ^ 2 * eval (stateAct (invCartan (Ux ξ hξ) i) (fun v => ((W v : ℝ) : ℂ)))
        (contractedQuadratic Pbase (NativeH.weightC i a)) := by
  rw [AnalyticDerivative.stressCovector_apply]
  have h1 : (∑ r : Fin 2184, ellRaw ξ hξ i a r *
      ((Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ) + t • W) r : ℝ) : ℂ)) =
      contractedF (ellRaw ξ hξ i a)
        ((fun v => ((pack (literalCfg ξ) v : ℝ) : ℂ)) + (t : ℂ) • fun v => ((W v : ℝ) : ℂ)) := by
    unfold contractedF
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← eval_real_row]
    rw [show (fun v => (((PartialAction.pack (literalCfg ξ) + t • W) v : ℝ) : ℂ)) =
      ((fun v => ((pack (literalCfg ξ) v : ℝ) : ℂ)) + (t : ℂ) • fun v => ((W v : ℝ) : ℂ)) from by
        funext v; simp]
  rw [h1, ellRaw, contractedF_transport, stateAct_add]
  exact contractedF_line_eq_quadratic_at_anchor Pbase (NativeH.weightC i a) i Pbase_solution
    (Pbase_equilibrium i a) (NativeH.hasAnchorSupport Pbase i a) _
    (transported_anchor ξ hξ i) _ (t : ℂ)

theorem originalF_ambient_differentiable : Differentiable ℝ Option2.NativeStress.originalF := by
  apply differentiable_pi.mpr
  intro r
  change Differentiable ℝ (fun x : Fin 1053 → ℝ =>
    eval x (NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r))
  induction NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r
    using MvPolynomial.induction_on with
  | C a => simpa only [eval_C] using
      (differentiable_const a : Differentiable ℝ (fun _ : Fin 1053 → ℝ => a))
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq
  | mul_X p v hp => simpa only [map_mul, eval_X] using hp.fun_mul (differentiable_apply v)

/-- A real-linear covector whose values on every line through `x` are `t² q(W)` kills the derivative. -/
theorem comp_fderiv_zero_of_lines (F : (Fin 1053 → ℝ) → (Fin 2184 → ℝ)) (hF : Differentiable ℝ F)
    (L : (Fin 2184 → ℝ) →L[ℝ] ℂ) (x : Fin 1053 → ℝ) (q : (Fin 1053 → ℝ) → ℂ)
    (hline : ∀ W (t : ℝ), L (F (x + t • W)) = (t : ℂ) ^ 2 * q W) :
    L.comp (fderiv ℝ F x) = 0 := by
  apply ContinuousLinearMap.ext
  intro W
  change (L.comp (fderiv ℝ F x)) W = 0
  have hchain : HasFDerivAt (fun X => L (F X)) (L.comp (fderiv ℝ F x)) x :=
    L.hasFDerivAt.comp x (hF x).hasFDerivAt
  have hl := hchain.hasLineDerivAt W
  change HasDerivAt (fun t : ℝ => L (F (x + t • W))) ((L.comp (fderiv ℝ F x)) W) 0 at hl
  have hfun : (fun t : ℝ => L (F (x + t • W))) = (fun t : ℝ => (t : ℂ) ^ 2 * q W) := by
    funext t; exact hline W t
  rw [hfun] at hl
  have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) (0 : ℝ) := by
    have hf : (fun t : ℝ => (t : ℂ)) = (Complex.ofRealCLM : ℝ → ℂ) := by
      funext t; exact (Complex.ofRealCLM_apply t).symm
    rw [hf]
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using
      (Complex.ofRealCLM.hasFDerivAt (x := (0 : ℝ))).hasDerivAt
  have hzero : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 * q W) 0 (0 : ℝ) := by
    simpa using (hcast.pow 2).mul_const (q W)
  exact hl.unique hzero

/-- **Equilibrium of the transported H covector at every unit phase** (resonant included), against
the actual Fréchet derivative of the unchanged originalF on all 1053 coordinates and 2184 rows. -/
theorem ellRaw_equilibrium (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3) :
    (AnalyticDerivative.stressCovector (ellRaw ξ hξ i a)).comp
      (fderiv ℝ Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ))) = 0 :=
  comp_fderiv_zero_of_lines _ originalF_ambient_differentiable _ _ _ fun W t =>
    transported_line ξ hξ i a W t

end Option2.NativeStress.HTPhaseComplete

end

#print axioms Option2.NativeStress.HTPhaseComplete.row_covariance
#print axioms Option2.NativeStress.HTPhaseComplete.ellRaw_contract
#print axioms Option2.NativeStress.HTPhaseComplete.contractedF_transport
#print axioms Option2.NativeStress.HTPhaseComplete.transported_anchor
#print axioms Option2.NativeStress.HTPhaseComplete.transported_line
#print axioms Option2.NativeStress.HTPhaseComplete.ellRaw_equilibrium
