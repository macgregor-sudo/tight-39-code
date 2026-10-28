module

public import TCBound

@[expose] public section

/-!
# A7: frame decomposition of tight codes and its converse 

Attribution: the 39-point code of thirteen orthogonal triples is Cohn–Kumar–Minton,
arXiv:1308.3188v4, Theorem 8.3 (p. 49); their Lemma 2.7 (p. 9) gives only the two-distance
consequence. The recognition of every tight code as thirteen frames is stated here; no prior
statement of it was found (a bounded search, not a novelty claim).

Forward: `gram P` is symmetric (`inner_comm`), has diagonal `1`, off-diagonal values `{0, 1/3}`
(`tight_overlap_values`), row sums `13` (`tight_row_sum`) and rank `≤ 27` (`rank_gram_le`), so the
partition theorem `CKM.CodeFramePartition.exists_equiv_triples` (reused from source) gives
`e`. For each block the three pure points have zero pairwise overlap, so
`⟨p + q + r - 1, p + q + r - 1⟩ = 3 - 2·3 + 3 = 0` and `p + q + r = 1` (`inner_self_eq_zero`); the
public `CompactAlbert.native_jordan_eq_zero_of_idempotents_sum` gives pairwise Jordan orthogonality.
The `Glennie.Frame` is assembled field by field (the private `native_frame_of_trace_idempotent_sum`
is not used). Converse: same-frame overlaps are `trace 0 = 0`, cross-frame overlaps are `1/3`.
-/

noncomputable section

namespace CKM.NativeTightCode

open Glennie

/-- Three pure points with pairwise zero overlap form an actual native Jordan frame. -/
theorem frame_of_zero_overlaps (p : Fin 3 → Albert) (hpure : ∀ a, IsPure (p a))
    (hz : ∀ a b, a ≠ b → inner (p a) (p b) = 0) : Frame p := by
  -- Basic facts on the three points.
  have hid : ∀ a, jordan (p a) (p a) = p a := fun a => (hpure a).1
  have hself : ∀ a, inner (p a) (p a) = 1 := fun a => inner_self_of_pure (hpure a)
  have hone : ∀ a, inner (p a) 1 = 1 := fun a => by rw [inner_one_right]; exact (hpure a).2
  have hone' : ∀ a, inner 1 (p a) = 1 := fun a => by rw [inner_comm]; exact hone a
  have h01 := hz 0 1 (by decide)
  have h02 := hz 0 2 (by decide)
  have h10 := hz 1 0 (by decide)
  have h12 := hz 1 2 (by decide)
  have h20 := hz 2 0 (by decide)
  have h21 := hz 2 1 (by decide)
  -- `⟨s, s⟩ = 3 - 6 + 3 = 0` for `s = p 0 + p 1 + p 2 - 1`.
  have hss : inner (p 0 + p 1 + p 2 - 1) (p 0 + p 1 + p 2 - 1) = 0 := by
    simp only [CKM.NativeDerivationTriality.Reuse.inner_sub_left,
      CKM.NativeDerivationTriality.Reuse.inner_sub_right,
      CKM.NativeDerivationTriality.Reuse.inner_add_left,
      CKM.NativeDerivationTriality.Reuse.inner_add_right,
      hself, hone, hone', inner_one_one, h01, h02, h10, h12, h20, h21]
    norm_num
  have hsum : p 0 + p 1 + p 2 = 1 := sub_eq_zero.mp ((inner_self_eq_zero _).mp hss)
  refine ⟨fun a => (hpure a).2, hid, ?_, hsum⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · show jordan (p 0) (p 1) = 0
    exact CompactAlbert.native_jordan_eq_zero_of_idempotents_sum _ _ (p 2) (hid _) (hid _)
        (hid _) hsum
  · show jordan (p 0) (p 2) = 0
    exact CompactAlbert.native_jordan_eq_zero_of_idempotents_sum _ _ (p 1) (hid _) (hid _)
        (hid _) (by rw [← hsum]; abel)
  · show jordan (p 1) (p 0) = 0
    exact CompactAlbert.native_jordan_eq_zero_of_idempotents_sum _ _ (p 2) (hid _) (hid _)
        (hid _) (by rw [← hsum]; abel)
  · exact absurd rfl hij
  · show jordan (p 1) (p 2) = 0
    exact CompactAlbert.native_jordan_eq_zero_of_idempotents_sum _ _ (p 0) (hid _) (hid _)
        (hid _) (by rw [← hsum]; abel)
  · show jordan (p 2) (p 0) = 0
    exact CompactAlbert.native_jordan_eq_zero_of_idempotents_sum _ _ (p 1) (hid _) (hid _)
        (hid _) (by rw [← hsum]; abel)
  · show jordan (p 2) (p 1) = 0
    exact CompactAlbert.native_jordan_eq_zero_of_idempotents_sum _ _ (p 0) (hid _) (hid _)
        (hid _) (by rw [← hsum]; abel)
  · exact absurd rfl hij

/-- **Equality case.** A 39-point pure code with the overlap bound splits into thirteen actual
native frames; cross-frame overlaps are `1/3`; distinct points have zero overlap exactly when they
lie in the same frame. -/
theorem tight_frame_decomposition (P : Fin 39 → Albert) (hpure : ∀ i, IsPure (P i))
    (hov : OverlapBound P) :
    ∃ e : Fin 39 ≃ Fin 13 × Fin 3,
      (∀ h, Frame fun a => P (e.symm (h, a))) ∧
      (∀ i j, (e i).1 ≠ (e j).1 → inner (P i) (P j) = 1 / 3) ∧
      (∀ i j, i ≠ j → (inner (P i) (P j) = 0 ↔ (e i).1 = (e j).1)) := by
  have hsymm : (gram P).IsSymm :=
    Matrix.IsSymm.ext fun i j => by simp only [gram, Matrix.of_apply]; exact inner_comm _ _
  have hdiag : ∀ i, gram P i i = 1 := fun i => by
    simp only [gram, Matrix.of_apply]; exact inner_self_of_pure (hpure i)
  have hoff : ∀ i j, i ≠ j → gram P i j = 0 ∨ gram P i j = (1 / 3 : ℝ) := fun i j hij => by
    simp only [gram, Matrix.of_apply]; exact tight_overlap_values P hpure hov i j hij
  have hrow : ∀ i, ∑ j, gram P i j = 13 := fun i => by
    simp only [gram, Matrix.of_apply]; exact tight_row_sum P hpure hov i
  obtain ⟨e, hiff, hzero, hcross⟩ :=
    CKM.CodeFramePartition.exists_equiv_triples (gram P) hsymm hdiag hoff hrow (rank_gram_le P)
  simp only [gram, Matrix.of_apply] at hiff hzero hcross
  refine ⟨e, fun h => ?_, hcross, hiff⟩
  refine frame_of_zero_overlaps _ (fun a => hpure _) fun a b hab => ?_
  have hne : e.symm (h, a) ≠ e.symm (h, b) := fun heq => hab (by simpa using heq)
  exact hzero _ _ hne (by simp)

/-- **Converse.** Thirteen native frames with cross-frame overlaps `1/3` satisfy the bound. -/
theorem overlapBound_of_frames (P : Fin 39 → Albert) (e : Fin 39 ≃ Fin 13 × Fin 3)
    (hframe : ∀ h, Frame fun a => P (e.symm (h, a)))
    (hcross : ∀ i j, (e i).1 ≠ (e j).1 → inner (P i) (P j) = 1 / 3) : OverlapBound P := by
  intro i j hij
  by_cases hb : (e i).1 = (e j).1
  · have hne : (e i).2 ≠ (e j).2 := fun h2 => hij (e.injective (Prod.ext hb h2))
    have h0 := (hframe (e i).1).orthogonal (e i).2 (e j).2 hne
    have hi : P (e.symm ((e i).1, (e i).2)) = P i := by simp
    have hj : P (e.symm ((e i).1, (e j).2)) = P j := by rw [hb]; simp
    simp only [hi, hj] at h0
    have : inner (P i) (P j) = 0 := by
      unfold inner
      rw [h0]
      simp [trace]
    rw [this]
    norm_num
  · exact (hcross i j hb).le

/-- **Equivalence.** For 39 native pure points, the overlap bound holds iff they split into
thirteen actual native frames with all cross-frame overlaps `1/3`. -/
theorem overlapBound_iff_frames (P : Fin 39 → Albert) (hpure : ∀ i, IsPure (P i)) :
    OverlapBound P ↔
      ∃ e : Fin 39 ≃ Fin 13 × Fin 3,
        (∀ h, Frame fun a => P (e.symm (h, a))) ∧
        (∀ i j, (e i).1 ≠ (e j).1 → inner (P i) (P j) = 1 / 3) := by
  constructor
  · intro hov
    obtain ⟨e, hframe, hcross, -⟩ := tight_frame_decomposition P hpure hov
    exact ⟨e, hframe, hcross⟩
  · rintro ⟨e, hframe, hcross⟩
    exact overlapBound_of_frames P e hframe hcross

#print axioms frame_of_zero_overlaps
#print axioms tight_frame_decomposition
#print axioms overlapBound_of_frames
#print axioms overlapBound_iff_frames

end CKM.NativeTightCode
