module

public import A3ElimHidden

@[expose] public section

/-!
# Elimination helpers III: frame bookkeeping and the shape of fixed variations

Frames `0..3` are the quartet frames `qFrame k`, frames `4..12` are `hiddenFrame l`. A variation fixed by
the compensated `R0` and satisfying the frame sums has zero hidden part on the quartet frames, and on
hidden frame `l` it is `(0, ω^t V_l/3)` with `V_l` the hidden component of `elimForward`.
-/

noncomputable section

namespace CKM.NativeFirstOrder.Elim

open NativePolynomial NativePolynomial.ConfigurationResiduals ConfigurationResidualIndices
open CompactAlbert

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "πp" => CompactAlbert.nativeTitsMatrixPair

/-- Read a `ZMod 3`-indexed matrix as a `Fin 3`-indexed Tits matrix (definitional identity). -/
def tm (M : UnitaryErrorBases.Mat) : TitsComplexMatrix := M

/-- Quartet frame `k` as one of the thirteen frames. -/
def qFrame (k : Fin 4) : Fin 13 := Fin.castLE (by omega) k

theorem qFrame_val (k : Fin 4) : (qFrame k).val = k.val := rfl

theorem hiddenFrame_val (l : UnitaryErrorBases.Label) :
    (hiddenFrame l).val = 4 + (hiddenFrameEquiv l).val := rfl

theorem qFrame_injective : Function.Injective qFrame := fun a b h =>
  Fin.ext (by have := congrArg Fin.val h; simpa [qFrame_val] using this)

theorem hiddenFrame_injective : Function.Injective hiddenFrame := fun a b h => by
  have := congrArg Fin.val h
  simp only [hiddenFrame_val] at this
  exact hiddenFrameEquiv.injective (Fin.ext (by omega))

theorem qFrame_lt_hiddenFrame (k : Fin 4) (l : UnitaryErrorBases.Label) :
    qFrame k < hiddenFrame l := by
  rw [Fin.lt_def, qFrame_val, hiddenFrame_val]; omega

theorem frame_cases (f : Fin 13) :
    (∃ k : Fin 4, f = qFrame k) ∨ (∃ l : UnitaryErrorBases.Label, f = hiddenFrame l) := by
  by_cases h : f.val < 4
  · exact Or.inl ⟨⟨f.val, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨hiddenFrameEquiv.symm ⟨f.val - 4, by omega⟩, Fin.ext ?_⟩
    rw [hiddenFrame_val, Equiv.apply_symm_apply]
    simp only
    omega

theorem point_cases (i : Fin 39) : ∃ f a, i = framePointIndex f a :=
  ⟨⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩, Fin.ext (by rw [framePointIndex_val]; simp; omega)⟩

/-- A labelled family assembled from quartet and hidden-frame data, in the `stdAnchored` order. -/
def assemble {X : Type*} (Fq : Fin 4 → Fin 3 → X) (Fh : UnitaryErrorBases.Label → Fin 3 → X)
    (i : Fin 39) : X :=
  if h : i.val < 12 then Fq ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩
  else Fh (hiddenFrameEquiv.symm ⟨i.val / 3 - 4, by have := i.isLt; omega⟩) ⟨i.val % 3, by omega⟩

theorem assemble_quartet {X : Type*} (Fq : Fin 4 → Fin 3 → X)
    (Fh : UnitaryErrorBases.Label → Fin 3 → X) (k : Fin 4) (a : Fin 3) :
    assemble Fq Fh (framePointIndex (qFrame k) a) = Fq k a := by
  have hv : (framePointIndex (qFrame k) a).val = 3 * k.val + a.val := rfl
  unfold assemble
  split_ifs with h
  swap
  · exfalso; rw [hv] at h; omega
  congr 1
  · exact Fin.ext (by simp only [hv]; omega)
  · exact Fin.ext (by simp only [hv]; omega)

theorem assemble_hidden {X : Type*} (Fq : Fin 4 → Fin 3 → X)
    (Fh : UnitaryErrorBases.Label → Fin 3 → X) (l : UnitaryErrorBases.Label) (a : Fin 3) :
    assemble Fq Fh (framePointIndex (hiddenFrame l) a) = Fh l a := by
  have hv : (framePointIndex (hiddenFrame l) a).val = 3 * (4 + (hiddenFrameEquiv l).val) + a.val :=
    rfl
  unfold assemble
  split_ifs with h
  · exfalso; rw [hv] at h; omega
  have hl : (⟨(framePointIndex (hiddenFrame l) a).val / 3 - 4, by
      have := (framePointIndex (hiddenFrame l) a).isLt; omega⟩ : Fin 9) = hiddenFrameEquiv l :=
    Fin.ext (by simp only [hv]; omega)
  rw [hl, Equiv.symm_apply_apply]
  congr 1
  exact Fin.ext (by simp only [hv]; omega)

theorem stdAnchored_eq_assemble (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) :
    stdAnchored q W = assemble (fun k t => includeHermitianMatrix (q k t))
      (fun l t => nativeComplementaryPoint ((ω ^ t.val) • W l)) := rfl

theorem stdAnchored_quartet (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (k : Fin 4) (a : Fin 3) :
    πp (stdAnchored q W (framePointIndex (qFrame k) a)) = ((q k a).val, 0) := by
  rw [stdAnchored_eq_assemble, assemble_quartet, includeHermitianMatrix_pair]

theorem stdAnchored_hidden (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (l : UnitaryErrorBases.Label) (a : Fin 3) :
    πp (stdAnchored q W (framePointIndex (hiddenFrame l) a)) =
      ((1 / 3 : ℂ) • (1 : TitsComplexMatrix), (1 / 3 : ℂ) • ((ω ^ a.val) • tm (W l))) := by
  rw [stdAnchored_eq_assemble, assemble_hidden]
  exact nativeComplementaryPoint_pair _

theorem framePointIndex_eq_finProdFinEquiv (f : Fin 13) (a : Fin 3) :
    framePointIndex f a = (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39) (f, a) :=
  Fin.ext (by rw [framePointIndex_val, finProdFinEquiv_apply_val]; ring)

theorem stdShift_apply (f : Fin 13) (a : Fin 3) :
    stdShift (framePointIndex f a) = framePointIndex f (a + if f.val < 4 then 0 else 2) := by
  unfold stdShift outcomeShift pointRelabel
  rw [framePointIndex_eq_finProdFinEquiv, framePointIndex_eq_finProdFinEquiv]
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodShear_apply,
    Equiv.refl_apply, Equiv.coe_addRight]

theorem stdShift_quartet (k : Fin 4) (a : Fin 3) :
    stdShift (framePointIndex (qFrame k) a) = framePointIndex (qFrame k) a := by
  have h : (qFrame k).val < 4 := by rw [qFrame_val]; exact k.isLt
  rw [stdShift_apply]
  simp only [h, ↓reduceIte, add_zero]

theorem stdShift_hidden (l : UnitaryErrorBases.Label) (a : Fin 3) :
    stdShift (framePointIndex (hiddenFrame l) a) = framePointIndex (hiddenFrame l) (a + 2) := by
  have h : ¬ (hiddenFrame l).val < 4 := by rw [hiddenFrame_val]; omega
  rw [stdShift_apply]
  simp only [h, ↓reduceIte]

theorem fixed_apply {δ : Fin 39 → Glennie.Albert} (hfix : δ ∈ fixedSpace (compensated R0 stdShift))
    (i : Fin 39) : R0 (δ (stdShift i)) = δ i := by
  rw [mem_fixedSpace] at hfix
  exact congrFun hfix i

theorem mem_fixed_of_apply {δ : Fin 39 → Glennie.Albert} (h : ∀ i, R0 (δ (stdShift i)) = δ i) :
    δ ∈ fixedSpace (compensated R0 stdShift) := by
  rw [mem_fixedSpace]
  exact funext h

theorem elimForward_fst_apply (δ : Fin 39 → Glennie.Albert) (k : Fin 4) (t : Fin 3) :
    (elimForward δ).1 k t = (πp (δ (framePointIndex (qFrame k) t))).1 := rfl

theorem elimForward_snd_apply (δ : Fin 39 → Glennie.Albert) (l : UnitaryErrorBases.Label) :
    (elimForward δ).2 l = (3 : ℝ) • (πp (δ (framePointIndex (hiddenFrame l) 0))).2 := rfl

/-- Fixed variations have zero hidden part on the quartet frames. -/
theorem fixed_quartet_pair {δ : Fin 39 → Glennie.Albert}
    (hfix : δ ∈ fixedSpace (compensated R0 stdShift)) (k : Fin 4) (a : Fin 3) :
    πp (δ (framePointIndex (qFrame k) a)) = ((elimForward δ).1 k a, 0) := by
  have h := fixed_apply hfix (framePointIndex (qFrame k) a)
  rw [stdShift_quartet] at h
  have h2 := congrArg (fun x => (πp x).2) h
  simp only [R0_pair] at h2
  have h3 : (ω - 1) • (πp (δ (framePointIndex (qFrame k) a))).2 = 0 := by
    rw [sub_smul, h2, one_smul, sub_self]
  have h4 := (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr omega_ne_one)
  exact Prod.ext rfl h4

/-- Fixed variations with frame sums are `(0, ω^t V_l/3)` on hidden frame `l`. -/
theorem fixed_hidden_pair {δ : Fin 39 → Glennie.Albert}
    (hfix : δ ∈ fixedSpace (compensated R0 stdShift))
    (hsum : ∀ f : Fin 13, (∑ a : Fin 3, δ (framePointIndex f a)) = 0)
    (l : UnitaryErrorBases.Label) (a : Fin 3) :
    πp (δ (framePointIndex (hiddenFrame l) a)) =
      (0, (1 / 3 : ℂ) • ((ω ^ a.val) • tm ((elimForward δ).2 l))) := by
  set P : Fin 3 → TitsMatrixPair := fun a => πp (δ (framePointIndex (hiddenFrame l) a)) with hP
  have hr : ∀ a, P a = ((P (a + 2)).1, ω • (P (a + 2)).2) := fun a => by
    simp only [hP]
    rw [← R0_pair, ← stdShift_hidden, fixed_apply hfix]
  have h0 := hr 0; have h1 := hr 1; have h2 := hr 2
  have e02 : (0 : Fin 3) + 2 = 2 := rfl
  have e12 : (1 : Fin 3) + 2 = 0 := rfl
  have e22 : (2 : Fin 3) + 2 = 1 := rfl
  rw [e02] at h0; rw [e12] at h1; rw [e22] at h2
  have hs : P 0 + P 1 + P 2 = 0 := by
    have := congrArg πp (hsum (hiddenFrame l))
    rw [map_sum, Fin.sum_univ_three, map_zero] at this
    exact this
  have hs1 := congrArg Prod.fst hs
  have a01 : (P 1).1 = (P 0).1 := by rw [h1]
  have a20 : (P 0).1 = (P 2).1 := by rw [h0]
  have b1 : (P 1).2 = ω • (P 0).2 := by rw [h1]
  have b2 : (P 2).2 = ω • (P 1).2 := by rw [h2]
  simp only [Prod.fst_add, Prod.fst_zero] at hs1
  rw [a01, ← a20] at hs1
  have hA : (P 0).1 = 0 := by
    have h3 : (3 : ℂ) • (P 0).1 = 0 := by rw [← hs1]; module
    exact (smul_eq_zero.mp h3).resolve_left (by norm_num)
  have hV : (1 / 3 : ℂ) • tm ((elimForward δ).2 l) = (P 0).2 := by
    change (1 / 3 : ℂ) • ((3 : ℝ) • (P 0).2) = (P 0).2
    rw [← Complex.coe_smul, smul_smul]
    norm_num
  change P a = _
  rw [smul_comm (1 / 3 : ℂ) (ω ^ a.val), hV]
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · exact Prod.ext hA (by simp)
  · exact Prod.ext (by rw [a01, hA]) (by rw [b1]; simp)
  · exact Prod.ext (by rw [← a20, hA])
      (by rw [b2, b1, smul_smul, ← pow_two]; rfl)

end CKM.NativeFirstOrder.Elim
