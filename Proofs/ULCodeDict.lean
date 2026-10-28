module

public import ULQuot
public import TCConsumer

@[expose] public section

/-!
# The code-space dictionary 

The tight-code dictionary uses `TCConsumer` and `CodeFramePartition`.

`tightLocus ⊆ Fin 39 → Fin 27 → ℝ` (accepted native upper coordinates, product topology): labelled
39-point configurations whose points `codePoint C i = upperCoordinateEquiv.symm (C i)` are native
pure points (`jordan p p = p`, `trace p = 1`) with distinct-pair overlap `inner (P i) (P j) ≤ 1/3`.

* `mem_zeroSet_iff_frames`: the original zero configurations are exactly the configurations of
  thirteen labelled native frames (`Glennie.Frame` on each label block `framePointIndex f ·`) with
  cross-frame overlap `1/3`.
* derived, not assumed: `zeroSet ⊆ tightLocus`, distinctness of the 39 points, uniqueness of the frame
  partition, and on `zeroSet` the zero-overlap relation is the literal block relation.
* `CodeGroup = G × S₃₉` (`G` the native group pointwise, `S₃₉` all point relabellings
  `e • C = C ∘ e⁻¹`) preserves `tightLocus`; `codeSetoid` is its orbit relation.
-/

noncomputable section

namespace CKM.NativeUnlabelledSlice

open Glennie NativePolynomial CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeTightCode
open Option2.NativeStress.AnalyticDerivative (originalF)
open scoped Topology

theorem codePoint_eq (C : Cfg) (i : Fin 39) : codePoint C i = fromUpperCoordinates (C i) := rfl


/-! ## Private helpers (prefix `uld_`) -/

/-- The coordinates of a point are the upper coordinates of the reconstructed native point. -/
private theorem uld_C_eq (C : Cfg) (i : Fin 39) : C i = upperCoordinates (codePoint C i) := by
  rw [codePoint_eq, upperCoordinates_fromUpperCoordinates]

/-- Idempotency row block is native idempotency. -/
private theorem uld_idem_iff (C : Cfg) (i : Fin 39) :
    CoordinateMaps.coordinateProduct (1 / 2 : ℝ) (C i) (C i) = C i ↔
      jordan (codePoint C i) (codePoint C i) = codePoint C i := by
  rw [← prodC_apply, uld_C_eq C i, prodC_upperCoordinates]
  constructor
  · intro h
    simpa only [fromUpperCoordinates_upperCoordinates] using congrArg fromUpperCoordinates h
  · intro h
    rw [h]

/-- Coordinate trace is native trace of the reconstructed point (same statement and proof as the
private `group_coordTrace` of the accepted `GSGroup`). -/
private theorem uld_trace (v : Fin 27 → ℝ) :
    CoordinateMaps.coordinateTrace v = trace (fromUpperCoordinates v) := by
  rw [CoordinateMaps.coordinateTrace_apply]
  rfl

/-- Pair rows are native trace pairings. -/
private theorem uld_pairing (C : Cfg) (i j : Fin 39) :
    CoordinateMaps.coordinatePairing (C i) (C j) = inner (codePoint C i) (codePoint C j) := by
  rw [uld_C_eq C i, uld_C_eq C j,
    CoordinateMaps.coordinatePairing_upperCoordinates_eq_native_trace]
  rfl

/-- Frame-sum row block is the native unit sum. -/
private theorem uld_sum_iff (C : Cfg) (f : Fin 13) :
    ∑ a : Fin 3, C (ConfigurationResiduals.framePointIndex f a) =
        (CoordinateMaps.coordinateUnit : Fin 27 → ℝ) ↔
      codePoint C (ConfigurationResiduals.framePointIndex f 0) +
          codePoint C (ConfigurationResiduals.framePointIndex f 1) +
          codePoint C (ConfigurationResiduals.framePointIndex f 2) = 1 := by
  have hU : (CoordinateMaps.coordinateUnit : Fin 27 → ℝ) = upperCoordinateEquiv (1 : Albert) := by
    funext k
    fin_cases k <;> rfl
  have hS : ∑ a : Fin 3, C (ConfigurationResiduals.framePointIndex f a) =
      upperCoordinateEquiv (∑ a : Fin 3, codePoint C (ConfigurationResiduals.framePointIndex f a)) := by
    rw [map_sum]
    simp only [codePoint, LinearEquiv.apply_symm_apply]
  rw [hS, hU, upperCoordinateEquiv.injective.eq_iff, Fin.sum_univ_three]

/-- Every label is `framePointIndex (i / 3) (i % 3)`. -/
private theorem uld_fpi (i : Fin 39) :
    ConfigurationResiduals.framePointIndex ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩ = i := by
  apply Fin.ext
  simp only [ConfigurationResiduals.framePointIndex_val]
  omega

private theorem uld_fpi_div (f : Fin 13) (a : Fin 3) :
    (ConfigurationResiduals.framePointIndex f a).val / 3 = f.val := by
  rw [ConfigurationResiduals.framePointIndex_val]
  omega

open ConfigurationResidualIndices in
/-- The original zero set is the `OriginalEquations` predicate at `h = 1/2`, `t = 1/3`. -/
private theorem uld_zeroSet_iff (C : Cfg) :
    C ∈ zeroSet ↔ PartialAction.OriginalEquations (1 / 2 : ℝ) (1 / 3 : ℝ) C := by
  have hF : ∀ q : FLabel,
      originalF C (fNumber q) = PartialAction.originalValue (1 / 2 : ℝ) (1 / 3 : ℝ) C q := by
    intro q
    change MvPolynomial.eval (PartialAction.pack C)
      (ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) (fNumber q)) = _
    rw [PartialAction.eval_fRow, Equiv.symm_apply_apply]
  rw [PartialAction.originalEquations_iff_values_zero]
  constructor
  · intro h q
    have h' : originalF C = 0 := h
    rw [← hF, h']
    rfl
  · intro h
    show originalF C = 0
    funext r
    obtain ⟨q, rfl⟩ := fNumber.surjective r
    rw [hF]
    exact h q

/-- Distinct points of one native frame have zero overlap. -/
private theorem uld_inner_frame {p : Fin 3 → Albert} (hp : Frame p) {a b : Fin 3} (hab : a ≠ b) :
    inner (p a) (p b) = 0 := by
  unfold Glennie.inner
  rw [hp.orthogonal a b hab]
  simp [trace]

/-- Labelled frames give pure points. -/
private theorem uld_pure_of_frames (C : Cfg)
    (hfr : ∀ f : Fin 13, Frame fun a => codePoint C (ConfigurationResiduals.framePointIndex f a))
    (i : Fin 39) : IsPure (codePoint C i) := by
  have h := hfr ⟨i.val / 3, by omega⟩
  have hi := uld_fpi i
  refine ⟨?_, ?_⟩
  · have := h.idempotent ⟨i.val % 3, by omega⟩
    simp only [hi] at this
    exact this
  · have := h.trace_one ⟨i.val % 3, by omega⟩
    simp only [hi] at this
    exact this

/-- Distinct labels in one literal block have zero overlap, given labelled frames. -/
private theorem uld_same_frame (C : Cfg)
    (hfr : ∀ f : Fin 13, Frame fun a => codePoint C (ConfigurationResiduals.framePointIndex f a))
    {i j : Fin 39} (hij : i ≠ j) (h : i.val / 3 = j.val / 3) :
    inner (codePoint C i) (codePoint C j) = 0 := by
  have hi := uld_fpi i
  have hj : ConfigurationResiduals.framePointIndex ⟨i.val / 3, by omega⟩ ⟨j.val % 3, by omega⟩ = j := by
    apply Fin.ext
    simp only [ConfigurationResiduals.framePointIndex_val]
    omega
  have hab : (⟨i.val % 3, by omega⟩ : Fin 3) ≠ ⟨j.val % 3, by omega⟩ := by
    intro hab
    apply hij
    simp only [Fin.mk.injEq] at hab
    apply Fin.ext
    omega
  have := uld_inner_frame (hfr ⟨i.val / 3, by omega⟩) hab
  simp only [hi, hj] at this
  exact this

/-- Same block of a frame decomposition: zero overlap. -/
private theorem uld_same_block {C : Cfg} (e : Fin 39 ≃ Fin 13 × Fin 3)
    (he : ∀ h, Frame fun a => codePoint C (e.symm (h, a))) {i j : Fin 39} (hij : i ≠ j)
    (hb : (e i).1 = (e j).1) : inner (codePoint C i) (codePoint C j) = 0 := by
  have hne : (e i).2 ≠ (e j).2 := fun h2 => hij (e.injective (Prod.ext hb h2))
  have h0 := uld_inner_frame (he (e i).1) hne
  have hi : codePoint C (e.symm ((e i).1, (e i).2)) = codePoint C i := by simp
  have hj : codePoint C (e.symm ((e i).1, (e j).2)) = codePoint C j := by rw [hb]; simp
  simp only [hi, hj] at h0
  exact h0

/-- A point outside block `h` of a frame decomposition of a tight code has overlap `1/3` with
every point of the block: the three overlaps lie in `{0, 1/3}` and sum to `trace = 1`. -/
private theorem uld_cross_block {C : Cfg} (hC : C ∈ tightLocus) (e : Fin 39 ≃ Fin 13 × Fin 3)
    (he : ∀ h, Frame fun a => codePoint C (e.symm (h, a))) (h : Fin 13) {j : Fin 39}
    (hj : (e j).1 ≠ h) (a : Fin 3) :
    inner (codePoint C j) (codePoint C (e.symm (h, a))) = 1 / 3 := by
  have hne : ∀ b, j ≠ e.symm (h, b) := fun b heq => hj (by rw [heq, Equiv.apply_symm_apply])
  have hsum : codePoint C (e.symm (h, 0)) + codePoint C (e.symm (h, 1)) +
      codePoint C (e.symm (h, 2)) = 1 := (he h).sum_unit
  have hj1 : inner (codePoint C j) (codePoint C (e.symm (h, 0)) + codePoint C (e.symm (h, 1)) +
      codePoint C (e.symm (h, 2))) = 1 := by
    rw [hsum, CKM.NativeTightCode.inner_one_right]
    exact (hC.1 j).2
  rw [CKM.NativeDerivationTriality.Reuse.inner_add_right,
    CKM.NativeDerivationTriality.Reuse.inner_add_right] at hj1
  have v0 := tight_overlap_values (codePoint C) hC.1 hC.2 j _ (hne 0)
  have v1 := tight_overlap_values (codePoint C) hC.1 hC.2 j _ (hne 1)
  have v2 := tight_overlap_values (codePoint C) hC.1 hC.2 j _ (hne 2)
  have h3 : inner (codePoint C j) (codePoint C (e.symm (h, 0))) = 1 / 3 ∧
      inner (codePoint C j) (codePoint C (e.symm (h, 1))) = 1 / 3 ∧
      inner (codePoint C j) (codePoint C (e.symm (h, 2))) = 1 / 3 := by
    rcases v0 with h0 | h0 <;> rcases v1 with h1 | h1 <;> rcases v2 with h2 | h2 <;>
      first
        | exact ⟨h0, h1, h2⟩
        | (exfalso; linarith)
  rcases (show ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 by decide) a with rfl | rfl | rfl
  · exact h3.1
  · exact h3.2.1
  · exact h3.2.2

/-- One direction of `frame_partition_unique`. -/
private theorem uld_block_imp {C : Cfg} (hC : C ∈ tightLocus) (e e' : Fin 39 ≃ Fin 13 × Fin 3)
    (he : ∀ h, Frame fun a => codePoint C (e.symm (h, a)))
    (he' : ∀ h, Frame fun a => codePoint C (e'.symm (h, a))) (i j : Fin 39)
    (hb : (e i).1 = (e j).1) : (e' i).1 = (e' j).1 := by
  by_cases hij : i = j
  · rw [hij]
  by_contra hne
  have h1 := uld_cross_block hC e' he' (e' i).1 (fun h => hne h.symm) (e' i).2
  simp only [Prod.mk.eta, Equiv.symm_apply_apply] at h1
  have h0 := uld_same_block e he hij hb
  rw [Glennie.inner_comm, h1] at h0
  norm_num at h0

/-! ### The code group on native points -/

private theorem uld_codePoint_codeAct (γ : autGroup × Equiv.Perm (Fin 39)) (C : Cfg) (i : Fin 39) :
    codePoint (actC (autVal γ.1) (permAct γ.2 C)) (γ.2 i) =
      coordEnd.symm (autVal γ.1) (codePoint C i) := by
  simp only [codePoint_eq, coordEnd_symm_apply, upperCoordinates_fromUpperCoordinates, actC_apply,
    permAct_apply, Equiv.symm_apply_apply]

private theorem uld_pure_iff {A : CEnd} (hA : A ∈ autC) (x : Albert) :
    IsPure (coordEnd.symm A x) ↔ IsPure x := by
  obtain ⟨hb, hj⟩ := (mem_autC_iff A).1 hA
  have ht := ((mem_autC_iff_isNativeAut A).1 hA).2.trace x
  unfold IsPure
  rw [← hj, hb.1.eq_iff, ht]

private theorem uld_inner_aut {A : CEnd} (hA : A ∈ autC) (x y : Albert) :
    inner (coordEnd.symm A x) (coordEnd.symm A y) = inner x y := by
  obtain ⟨-, hj⟩ := (mem_autC_iff A).1 hA
  have ht := ((mem_autC_iff_isNativeAut A).1 hA).2.trace (jordan x y)
  rw [Glennie.inner, Glennie.inner, ← hj, ht]

/-! ## The dictionary -/

/-- **Original zero configurations are thirteen labelled native frames with cross overlap `1/3`.** -/
theorem mem_zeroSet_iff_frames (C : Cfg) :
    C ∈ zeroSet ↔
      (∀ f : Fin 13, Frame fun a => codePoint C (ConfigurationResiduals.framePointIndex f a)) ∧
        ∀ i j : Fin 39, i.val / 3 ≠ j.val / 3 → inner (codePoint C i) (codePoint C j) = 1 / 3 := by
  rw [uld_zeroSet_iff]
  constructor
  · intro hC
    have hpure : ∀ i, IsPure (codePoint C i) := fun i =>
      ⟨(uld_idem_iff C i).1 (hC.idempotent i), by
        rw [codePoint_eq, ← uld_trace]; exact hC.trace_one i⟩
    have hpair : ∀ i j : Fin 39, i ≠ j → inner (codePoint C i) (codePoint C j) =
        if i.val / 3 = j.val / 3 then 0 else 1 / 3 := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with h | h
      · have := hC.pair ⟨(i, j), h⟩
        rw [uld_pairing] at this
        exact this
      · have := hC.pair ⟨(j, i), h⟩
        rw [uld_pairing, Glennie.inner_comm] at this
        rw [this]
        by_cases hji : j.val / 3 = i.val / 3
        · simp [hji]
        · have hij' : ¬ i.val / 3 = j.val / 3 := fun h' => hji h'.symm
          simp [hji, hij']
    refine ⟨fun f => frame_of_zero_overlaps _ (fun a => hpure _) fun a b hab => ?_,
      fun i j hij => ?_⟩
    · have hne : ConfigurationResiduals.framePointIndex f a ≠
          ConfigurationResiduals.framePointIndex f b := by
        intro h
        apply hab
        apply Fin.ext
        have := congrArg Fin.val h
        simp only [ConfigurationResiduals.framePointIndex_val] at this
        omega
      rw [hpair _ _ hne]
      simp [uld_fpi_div]
    · have hne : i ≠ j := fun h => hij (by rw [h])
      rw [hpair i j hne]
      simp [hij]
  · rintro ⟨hfr, hcross⟩
    refine ⟨fun i => (uld_idem_iff C i).2 (uld_pure_of_frames C hfr i).1,
      fun i => by rw [uld_trace]; exact (uld_pure_of_frames C hfr i).2,
      fun f => (uld_sum_iff C f).2 (hfr f).sum_unit, fun ij => ?_⟩
    rw [uld_pairing]
    split_ifs with h
    · exact uld_same_frame C hfr (ne_of_lt ij.2) h
    · exact hcross _ _ h

/-- On the zero set the partition relation is the literal frame relation. -/
theorem zeroRel_iff_of_mem_zeroSet {C : Cfg} (hC : C ∈ zeroSet) (i j : Fin 39) :
    zeroRel C i j ↔ i.val / 3 = j.val / 3 := by
  obtain ⟨hfr, hcross⟩ := (mem_zeroSet_iff_frames C).1 hC
  unfold zeroRel
  constructor
  · rintro (rfl | h0)
    · rfl
    · by_contra hne
      rw [hcross i j hne] at h0
      norm_num at h0
  · intro h
    by_cases hij : i = j
    · exact Or.inl hij
    · exact Or.inr (uld_same_frame C hfr hij h)

theorem zeroSet_subset_tightLocus : zeroSet ⊆ tightLocus := by
  intro C hC
  obtain ⟨hfr, hcross⟩ := (mem_zeroSet_iff_frames C).1 hC
  refine ⟨uld_pure_of_frames C hfr, fun i j hij => ?_⟩
  by_cases h : i.val / 3 = j.val / 3
  · rw [uld_same_frame C hfr hij h]
    norm_num
  · rw [hcross i j h]

/-- Derived distinctness: the 39 points of a tight code are distinct. -/
theorem tightLocus_injective {C : Cfg} (hC : C ∈ tightLocus) : Function.Injective (codePoint C) := by
  intro i j hij
  by_contra hne
  have h : inner (codePoint C i) (codePoint C j) ≤ 1 / 3 := hC.2 i j hne
  rw [hij, inner_self_of_pure (hC.1 j)] at h
  norm_num at h

/-- Derived uniqueness: any two frame decompositions of a tight code have the same blocks. -/
theorem frame_partition_unique {C : Cfg} (hC : C ∈ tightLocus) (e e' : Fin 39 ≃ Fin 13 × Fin 3)
    (he : ∀ h, Frame fun a => codePoint C (e.symm (h, a)))
    (he' : ∀ h, Frame fun a => codePoint C (e'.symm (h, a))) :
    ∀ i j, (e i).1 = (e j).1 ↔ (e' i).1 = (e' j).1 := by
  intro i j
  exact ⟨uld_block_imp hC e e' he he' i j, uld_block_imp hC e' e he' he i j⟩

/-! ## The literal code -/

theorem codePoint_literalCfg (ξ : Fin 4 → ℂ) (i : Fin 39) :
    codePoint (literalCfg ξ) i = literalPoint ξ i := by
  rw [codePoint_eq]
  exact fromUpperCoordinates_upperCoordinates (literalPoint ξ i)

theorem literalCfg_mem_tightLocus (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : literalCfg ξ ∈ tightLocus :=
  zeroSet_subset_tightLocus (literalCfg_mem_zeroSet ξ hξ)

/-! ## The code group -/

/-- `G × S₃₉`. -/
abbrev CodeGroup := autGroup × Equiv.Perm (Fin 39)

/-- `(g, e) • C = g • (e • C)`. -/
def codeAct (γ : CodeGroup) (C : Cfg) : Cfg := actC (autVal γ.1) (permAct γ.2 C)

theorem codeAct_mem_tightLocus_iff (γ : CodeGroup) (C : Cfg) :
    codeAct γ C ∈ tightLocus ↔ C ∈ tightLocus := by
  have hA := autVal_mem γ.1
  have hpt := uld_codePoint_codeAct γ C
  constructor
  · rintro ⟨hp, hov⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · have := hp (γ.2 i)
      rw [codeAct, hpt, uld_pure_iff hA] at this
      exact this
    · have : inner (codePoint (codeAct γ C) (γ.2 i)) (codePoint (codeAct γ C) (γ.2 j)) ≤ 1 / 3 :=
        hov (γ.2 i) (γ.2 j) fun h => hij (γ.2.injective h)
      rw [codeAct, hpt, hpt, uld_inner_aut hA] at this
      exact this
  · rintro ⟨hp, hov⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · obtain ⟨i', rfl⟩ := γ.2.surjective i
      rw [codeAct, hpt, uld_pure_iff hA]
      exact hp i'
    · obtain ⟨i', rfl⟩ := γ.2.surjective i
      obtain ⟨j', rfl⟩ := γ.2.surjective j
      rw [codeAct, hpt, hpt, uld_inner_aut hA]
      exact hov i' j' fun h => hij (by rw [h])

/-- The unlabelled code relation. -/
def codeSetoid : Setoid tightLocus where
  r C C' := ∃ γ : CodeGroup, codeAct γ C = C'
  iseqv := by
    constructor
    · intro C
      refine ⟨1, ?_⟩
      funext i
      rfl
    · rintro C C' ⟨γ, hγ⟩
      refine ⟨γ⁻¹, ?_⟩
      rw [← hγ]
      funext i
      simp only [codeAct, actC_apply, permAct_apply, Prod.fst_inv, Prod.snd_inv,
        Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.symm_apply_apply]
      have h1 : autVal γ.1⁻¹ * autVal γ.1 = 1 := by
        rw [← autVal_mul, inv_mul_cancel, autVal_one]
      exact DFunLike.congr_fun h1 _
    · rintro C C' C'' ⟨γ, hγ⟩ ⟨δ, hδ⟩
      refine ⟨δ * γ, ?_⟩
      rw [← hδ, ← hγ]
      funext i
      rfl

end CKM.NativeUnlabelledSlice

#print axioms CKM.NativeUnlabelledSlice.mem_zeroSet_iff_frames
#print axioms CKM.NativeUnlabelledSlice.zeroRel_iff_of_mem_zeroSet
#print axioms CKM.NativeUnlabelledSlice.zeroSet_subset_tightLocus
#print axioms CKM.NativeUnlabelledSlice.tightLocus_injective
#print axioms CKM.NativeUnlabelledSlice.frame_partition_unique
#print axioms CKM.NativeUnlabelledSlice.codeAct_mem_tightLocus_iff
#print axioms CKM.NativeUnlabelledSlice.codeSetoid
#print axioms CKM.NativeUnlabelledSlice.codePoint_literalCfg
#print axioms CKM.NativeUnlabelledSlice.literalCfg_mem_tightLocus
