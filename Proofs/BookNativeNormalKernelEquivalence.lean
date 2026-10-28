module

public import BookNativeAxisBridge

@[expose] public section

/-! Actual fixed-seed common tangent × unchanged Book blocks ≃L native normal kernel.
The four family images cover by the accepted total span, with dimensions 4+24=28.
No rank, complementarity, character intertwining, or surrogate-matrix premise. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.NativeNormalKernelBridge
open TangentCoordinates CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration

theorem finrank_triple_real : Module.finrank ℝ Triple = 6 := by
  rw [finrank_real_of_complex]
  norm_num [Triple]

theorem finrank_blocks_real : Module.finrank ℝ Blocks = 24 := by
  rw [Module.finrank_pi_fintype]
  norm_num [finrank_triple_real]

theorem projectedBook_axis_mem_fixQ (H : Fin 4) (u : Triple) :
    (projectedBook (Pi.single H u) : Cfg) ∈ fixQ exactPhases H := by
  rw [← range_sliceFamDer exactPhases_good H]
  refine ⟨projectedSimultaneousFamily H (axisParameters H u), ⟨(axisParameters H u, 0), ?_⟩, ?_⟩
  · rw [sliceFamDer_eq_normalProjection]
    change normalProjection (preDer exactPhases exactPhases_unit H (axisParameters H u, 0, 0)) = _
    rw [preDer_apply, projectedSimultaneousFamily_eq_left]
  · exact congrArg Subtype.val (projectedBook_axis H u).symm

def familyAmbient (H : Fin 4) : (fixQK exactPhases × Triple) →L[ℝ] Cfg :=
  (fixQK exactPhases).subtypeL.coprod
    ((tanN exactPhases).subtypeL.comp
      (projectedBook.comp (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => Triple) H)))

def familyCommonMap (H : Fin 4) : (fixQK exactPhases × Triple) →L[ℝ] fixQ exactPhases H :=
  (familyAmbient H).codRestrict (fixQ exactPhases H) (by
    rintro ⟨c, u⟩
    apply (fixQ exactPhases H).add_mem
    · have hle : fixQK exactPhases ≤ fixQ exactPhases H := by
        rw [fixQK_eq_iInf]
        exact iInf_le _ H
      exact hle c.property
    · exact projectedBook_axis_mem_fixQ H u)

theorem familyCommonMap_coe (H : Fin 4) (c : fixQK exactPhases) (u : Triple) :
    (familyCommonMap H (c, u) : Cfg) = (c : Cfg) + (projectedBook (Pi.single H u) : Cfg) := rfl

theorem familyCommonMap_injective (H : Fin 4) : Function.Injective (familyCommonMap H) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨c, u⟩ hcu
  have he : (c : Cfg) + (projectedBook (Pi.single H u) : Cfg) = 0 :=
    congrArg Subtype.val hcu
  have hc : (projectedBook (Pi.single H u) : Cfg) ∈ fixQK exactPhases := by
    rw [eq_neg_of_add_eq_zero_right he]
    exact (fixQK exactPhases).neg_mem c.property
  have hu := projectedBook_axis_inter_common H u hc
  subst u
  have hc0 : c = 0 := by
    apply Subtype.ext
    simpa using he
  exact Prod.ext hc0 rfl

/-- Each native family is exactly its common tangent plus the actual six real Book axis directions. -/
theorem familyCommonMap_bijective (H : Fin 4) : Function.Bijective (familyCommonMap H) := by
  have hd : Module.finrank ℝ (fixQK exactPhases × Triple) =
      Module.finrank ℝ (fixQ exactPhases H) := by
    rw [Module.finrank_prod, finrank_fixQK exactPhases_good, finrank_triple_real,
      finrank_fixQ exactPhases_good H]
  exact ⟨familyCommonMap_injective H,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1
      (familyCommonMap_injective H)⟩

/-- The accepted total four-family span proves joint surjectivity, not merely pairwise separation. -/
theorem bookCommonMap_surjective : Function.Surjective bookCommonMap := by
  let M : (fixQK exactPhases × Blocks) →L[ℝ] Cfg :=
    (tanN exactPhases).subtypeL.comp bookCommonMap
  have hspan : tanN exactPhases ≤ LinearMap.range M.toLinearMap := by
    rw [← iSup_fixQ exactPhases_unit]
    apply iSup_le
    intro H w hw
    obtain ⟨⟨c, u⟩, he⟩ := (familyCommonMap_bijective H).2 ⟨w, hw⟩
    refine ⟨(c, Pi.single H u), ?_⟩
    exact congrArg Subtype.val he
  intro n
  obtain ⟨p, hp⟩ := hspan n.property
  exact ⟨p, Subtype.ext hp⟩

theorem bookCommonMap_bijective : Function.Bijective bookCommonMap := by
  have hd : Module.finrank ℝ (fixQK exactPhases × Blocks) =
      Module.finrank ℝ (tanN exactPhases) := by
    rw [Module.finrank_prod, finrank_fixQK exactPhases_good, finrank_blocks_real,
      finrank_tanN exactPhases_good]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).2
    bookCommonMap_surjective, bookCommonMap_surjective⟩

/-- Genuine continuous real-linear equivalence with the original Book component unchanged. -/
def bookNormalKernelEquiv : (fixQK exactPhases × Blocks) ≃L[ℝ] tanN exactPhases :=
  (LinearEquiv.ofBijective bookCommonMap.toLinearMap bookCommonMap_bijective).toContinuousLinearEquiv

theorem bookNormalKernelEquiv_toContinuousLinearMap :
    bookNormalKernelEquiv.toContinuousLinearMap = bookCommonMap := rfl

/-- Exact native commutative formula: common tangent plus normal projection of unpacked realV. -/
theorem bookNormalKernelEquiv_apply (c : fixQK exactPhases) (z : Blocks) :
    (bookNormalKernelEquiv (c, z) : Cfg) =
      (c : Cfg) + (normalProjection (unpackNative (realV z)) : Cfg) := rfl

theorem native_book_orbit_common_separation (z : Blocks)
    (hz : bookDirection z ∈ orbitC exactPhases ⊔ fixQK exactPhases) : z = 0 :=
  bookCommonMap_injective_iff_native_separation.1 bookCommonMap_bijective.1 z hz

theorem projectedBook_injective : Function.Injective projectedBook := by
  intro x y hxy
  have h : bookCommonMap (0, x) = bookCommonMap (0, y) := by
    change commonInclusion 0 + projectedBook x = commonInclusion 0 + projectedBook y
    rw [hxy]
  exact congrArg Prod.snd (bookCommonMap_bijective.1 h)

/-- The full native normal-kernel decomposition exists uniquely. -/
theorem unique_book_common_decomposition (n : tanN exactPhases) :
    ∃! p : fixQK exactPhases × Blocks, bookCommonMap p = n := by
  obtain ⟨p, hp⟩ := bookCommonMap_surjective n
  exact ⟨p, hp, fun q hq => bookCommonMap_bijective.1 (hq.trans hp.symm)⟩

end Option2.NativeStress.BookHT.NativeNormalKernelBridge
#check Option2.NativeStress.BookHT.NativeNormalKernelBridge.bookNormalKernelEquiv
#check Option2.NativeStress.BookHT.NativeNormalKernelBridge.bookNormalKernelEquiv_apply
#check Option2.NativeStress.BookHT.NativeNormalKernelBridge.native_book_orbit_common_separation
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.familyCommonMap_bijective
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.bookNormalKernelEquiv
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.native_book_orbit_common_separation
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.unique_book_common_decomposition
