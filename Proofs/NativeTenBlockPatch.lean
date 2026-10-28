module

public import NativeSliceChartIsolation

@[expose] public section

/-! Extract a genuine open ten-parameter homeomorphism from the actual A5
slice block after whole-slice isolation.  -/
noncomputable section
namespace Option2.NativeStress.TenBlockPatchA7
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open SliceChartIsolationA7
open scoped Topology

abbrev TenParam := (Fin 4 → ℝ) × (Fin 6 → ℝ)
def blockInsert (H : Fin 4) (a : TenParam) : SliceModel :=
  (a.1,(fun j => if j = H then a.2 else 0),0)
def blockExtract (H : Fin 4) (z : SliceModel) : TenParam := (z.1,z.2.1 H)

private theorem continuous_blockInsert (H : Fin 4) : Continuous (blockInsert H) := by
  apply Continuous.prodMk continuous_fst
  apply Continuous.prodMk _ continuous_const
  apply continuous_pi
  intro j
  by_cases hj : j = H
  · simpa [blockInsert,hj] using (continuous_snd : Continuous (Prod.snd : TenParam → _))
  · simpa [blockInsert,hj] using (continuous_const : Continuous (fun _ : TenParam => (0 : Fin 6 → ℝ)))
private theorem continuous_blockExtract (H : Fin 4) : Continuous (blockExtract H) :=
  continuous_fst.prodMk ((continuous_apply H).comp (continuous_fst.comp continuous_snd))
private theorem blockExtract_insert (H : Fin 4) (a : TenParam) :
    blockExtract H (blockInsert H a) = a := by simp [blockExtract,blockInsert]
private theorem blockInsert_mem (H : Fin 4) (a : TenParam) :
    blockInsert H a ∈ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H := by
  exact ⟨fun j hj => ite_eq_right hj,rfl⟩
private theorem blockInsert_extract (H : Fin 4) (z : SliceModel)
    (hz : z ∈ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H) :
    blockInsert H (blockExtract H z) = z := by
  change (z.1,(fun j => if j = H then z.2.1 H else 0),0) = z
  refine Prod.ext rfl ?_
  apply Prod.ext _ hz.2.symm
  funext j
  by_cases hj : j = H
  · simp [hj]
  · exact (ite_eq_right hj).trans (hz.1 j hj).symm

/-- The isolated actual chart block supplies an open ten-parameter patch. -/
theorem ten_block_patch {ξ : Fin 4 → ℂ} (H : Fin 4)
    (Φ : OpenPartialHomeomorph SliceModel ↥(normalC ξ))
    (V : Set ↥(normalC ξ)) (hV : IsOpen V) (hVT : V ⊆ Φ.target)
    (hne : (V ∩ normalZero ξ).Nonempty)
    (heq : V ∩ normalZero ξ = V ∩ (Φ '' (Φ.source ∩
      familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H))) :
    ∃ U : Set TenParam, IsOpen U ∧ U.Nonempty ∧ Nonempty (U ≃ₜ ↥(V ∩ normalZero ξ)) := by
  let U := blockInsert H ⁻¹' (Φ.source ∩ Φ ⁻¹' V)
  have hU : IsOpen U := (Φ.isOpen_inter_preimage hV).preimage (continuous_blockInsert H)
  have hf : ∀ a ∈ U, Φ (blockInsert H a) ∈ V ∩ normalZero ξ := by
    intro a ha
    rw [heq]
    exact ⟨ha.2,⟨blockInsert H a,⟨ha.1,blockInsert_mem H a⟩,rfl⟩⟩
  have hi : ∀ n ∈ V ∩ normalZero ξ,
      Φ.symm n ∈ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H := by
    intro n hn
    rw [heq] at hn
    obtain ⟨z,⟨hz,hzb⟩,rfl⟩ := hn.2
    rwa [Φ.left_inv hz]
  have hg : ∀ n ∈ V ∩ normalZero ξ, blockExtract H (Φ.symm n) ∈ U := by
    intro n hn
    change blockInsert H (blockExtract H (Φ.symm n)) ∈ Φ.source ∩ Φ ⁻¹' V
    rw [blockInsert_extract H _ (hi n hn)]
    exact ⟨Φ.map_target (hVT hn.1),by change Φ (Φ.symm n) ∈ V; rw [Φ.right_inv (hVT hn.1)]; exact hn.1⟩
  let e : U ≃ₜ ↥(V ∩ normalZero ξ) :=
    { toFun := fun a => ⟨Φ (blockInsert H a),hf a a.2⟩
      invFun := fun n => ⟨blockExtract H (Φ.symm n),hg n n.2⟩
      left_inv := fun a => Subtype.ext (by
        change blockExtract H (Φ.symm (Φ (blockInsert H a))) = a
        rw [Φ.left_inv a.2.1,blockExtract_insert])
      right_inv := fun n => Subtype.ext (by
        change Φ (blockInsert H (blockExtract H (Φ.symm n))) = n
        rw [blockInsert_extract H _ (hi n n.2),Φ.right_inv (hVT n.2.1)])
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact Φ.continuousOn.comp_continuous
          ((continuous_blockInsert H).comp continuous_subtype_val) (fun a => a.2.1)
      continuous_invFun := by
        apply continuous_iff_continuousAt.2
        intro n
        apply ContinuousAt.codRestrict
        exact (continuous_blockExtract H).continuousAt.comp
          ((Φ.continuousAt_symm (hVT n.2.1)).comp continuous_subtype_val.continuousAt) }
  obtain ⟨n,hn⟩ := hne
  exact ⟨U,hU,⟨_,(e.symm ⟨n,hn⟩).2⟩,⟨e⟩⟩

#print axioms ten_block_patch
end Option2.NativeStress.TenBlockPatchA7
