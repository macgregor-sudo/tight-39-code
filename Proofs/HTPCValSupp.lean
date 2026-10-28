module

public import HTPCValMat

@[expose] public section

/-! Support and unit statements for `N_j` from the kernel checks `nCheck_all` (first-party). -/

set_option autoImplicit false

namespace Option2.NativeStress.HTPhaseComplete

theorem litZ_ne_zero_mem (l : List KLit) (k c : Fin 27) (h : litZ l k c ≠ 0) :
    ∃ e ∈ l, e.1 = k.val ∧ e.2.1 = c.val := by
  unfold litZ findLit at h
  cases hf : l.find? (fun e => e.1 == k.val && e.2.1 == c.val) with
  | none => rw [hf] at h; simp at h
  | some e =>
    refine ⟨e, List.mem_of_find?_eq_some hf, ?_⟩
    have := List.find?_some hf
    simpa [Bool.and_eq_true, beq_iff_eq] using this

theorem nCheck_spec (j : Fin 24) :
    ∃ pr kp, aPairOf j = some pr ∧ kPairOf j = some kp ∧ pr.2.1 = kp.2.1 ∧ sheetOf j = pr.1 ∧
      (∀ c n : Fin 27, (jMem pr.1 c && jMem pr.1 n) = false →
        iAt pr.2.2.2.1 c n = litZ kp.2.2.2.1 c n ∧ iAt pr.2.2.2.2 c n = litZ kp.2.2.2.2 c n) ∧
      (∀ c : Fin 27, (iAt pr.2.2.2.1 c 0 - litZ kp.2.2.2.1 c 0) + (iAt pr.2.2.2.1 c 1 - litZ kp.2.2.2.1 c 1) +
          (iAt pr.2.2.2.1 c 2 - litZ kp.2.2.2.1 c 2) = 0 ∧
        (iAt pr.2.2.2.2 c 0 - litZ kp.2.2.2.2 c 0) + (iAt pr.2.2.2.2 c 1 - litZ kp.2.2.2.2 c 1) +
          (iAt pr.2.2.2.2 c 2 - litZ kp.2.2.2.2 c 2) = 0) := by
  have hc := nCheck_all j
  unfold nCheck at hc
  cases ha : aPairOf j with
  | none => rw [ha] at hc; simp at hc
  | some pr =>
    cases hk : kPairOf j with
    | none => rw [ha, hk] at hc; simp at hc
    | some kp =>
      rw [ha, hk] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨⟨-, h2⟩, -⟩, hA⟩, hK⟩, hU⟩ := hc
      refine ⟨pr, kp, rfl, rfl, h2, by simp [sheetOf, ha], ?_, ?_⟩
      · intro c n hJ
        -- if either difference were nonzero, some listed position would be (c, n)
        by_contra hne
        have hor : iAt pr.2.2.2.1 c n ≠ litZ kp.2.2.2.1 c n ∨ iAt pr.2.2.2.2 c n ≠ litZ kp.2.2.2.2 c n := by
          by_contra h'; push_neg at h'; exact hne h'
        have okcn : ((jMem pr.1 c && jMem pr.1 n) ||
            ((iAt pr.2.2.2.1 c n - litZ kp.2.2.2.1 c n == 0) && (iAt pr.2.2.2.2 c n - litZ kp.2.2.2.2 c n == 0))) = true := by
          have pos : (∃ e ∈ pr.2.2.2.1 ++ pr.2.2.2.2, e.1 = c ∧ e.2.1 = n) ∨
              (∃ e ∈ kp.2.2.2.1 ++ kp.2.2.2.2, e.1 = c.val ∧ e.2.1 = n.val) := by
            rcases hor with h | h
            · by_cases h0 : iAt pr.2.2.2.1 c n = 0
              · have : litZ kp.2.2.2.1 c n ≠ 0 := by rw [h0] at h; exact fun h' => h h'.symm
                obtain ⟨e, he, h1, h2⟩ := litZ_ne_zero_mem _ c n this
                exact Or.inr ⟨e, List.mem_append_left _ he, h1, h2⟩
              · obtain ⟨e, he, h1, h2⟩ := iAt_ne_zero_mem _ c n h0
                exact Or.inl ⟨e, List.mem_append_left _ he, h1, h2⟩
            · by_cases h0 : iAt pr.2.2.2.2 c n = 0
              · have : litZ kp.2.2.2.2 c n ≠ 0 := by rw [h0] at h; exact fun h' => h h'.symm
                obtain ⟨e, he, h1, h2⟩ := litZ_ne_zero_mem _ c n this
                exact Or.inr ⟨e, List.mem_append_right _ he, h1, h2⟩
              · obtain ⟨e, he, h1, h2⟩ := iAt_ne_zero_mem _ c n h0
                exact Or.inl ⟨e, List.mem_append_right _ he, h1, h2⟩
          rcases pos with ⟨e, he, rfl, rfl⟩ | ⟨e, he, h1, h2⟩
          · exact hA e he
          · have := hK e he
            have hlt : e.1 < 27 ∧ e.2.1 < 27 := ⟨h1 ▸ c.isLt, h2 ▸ n.isLt⟩
            rw [dif_pos hlt] at this
            have ec : (⟨e.1, hlt.1⟩ : Fin 27) = c := Fin.ext h1
            have en : (⟨e.2.1, hlt.2⟩ : Fin 27) = n := Fin.ext h2
            rw [ec, en] at this; exact this
        rw [hJ, Bool.false_or, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at okcn
        exact hne ⟨by linarith [okcn.1], by linarith [okcn.2]⟩
      · intro c
        exact hU c (List.mem_finRange c)

theorem nZ_eq (j : Fin 24) (k c : Fin 27) :
    ∃ pr kp, aPairOf j = some pr ∧ kPairOf j = some kp ∧ pr.2.1 = kp.2.1 ∧
      nZ j k c = (if pr.2.1 = j.val then
        (⟨iAt pr.2.2.2.1 k c - litZ kp.2.2.2.1 k c, -(iAt pr.2.2.2.2 k c - litZ kp.2.2.2.2 k c)⟩ : GaussianInt)
        else ⟨-(iAt pr.2.2.2.1 k c - litZ kp.2.2.2.1 k c), -(iAt pr.2.2.2.2 k c - litZ kp.2.2.2.2 k c)⟩) := by
  obtain ⟨pr, kp, ha, hk, h2, -, -, -⟩ := nCheck_spec j
  refine ⟨pr, kp, ha, hk, h2, ?_⟩
  unfold nZ aZ kZ; rw [ha, hk]; dsimp only
  rw [h2]
  split_ifs <;> ext <;> simp <;> ring

/-- **Support of `N_j`.** -/
theorem nZ_support (j : Fin 24) (c n : Fin 27) (h : nZ j c n ≠ 0) :
    jMem (sheetOf j) c = true ∧ jMem (sheetOf j) n = true := by
  obtain ⟨pr, kp, ha, hk, h2, hs, hsupp, -⟩ := nCheck_spec j
  rw [hs]
  by_contra hJ
  have hJ' : (jMem pr.1 c && jMem pr.1 n) = false := by
    cases h1 : jMem pr.1 c <;> cases h2 : jMem pr.1 n <;> simp_all
  obtain ⟨e1, e2⟩ := hsupp c n hJ'
  obtain ⟨pr', kp', ha', hk', -, hz⟩ := nZ_eq j c n
  rw [ha] at ha'; rw [hk] at hk'; cases ha'; cases hk'
  apply h; rw [hz, e1, e2]; split_ifs <;> ext <;> simp

/-- **`N_j` kills the unit.** -/
theorem nZ_unit (j : Fin 24) (c : Fin 27) : nZ j c 0 + nZ j c 1 + nZ j c 2 = 0 := by
  obtain ⟨pr, kp, ha, hk, h2, -, -, hU⟩ := nCheck_spec j
  obtain ⟨u1, u2⟩ := hU c
  have r0 := nZ_eq j c 0; have r1 := nZ_eq j c 1; have r2 := nZ_eq j c 2
  obtain ⟨p0, k0, a0, b0, -, z0⟩ := r0; obtain ⟨p1, k1, a1, b1, -, z1⟩ := r1; obtain ⟨p2, k2, a2, b2, -, z2⟩ := r2
  rw [ha] at a0 a1 a2; rw [hk] at b0 b1 b2; cases a0; cases a1; cases a2; cases b0; cases b1; cases b2
  rw [z0, z1, z2]
  split_ifs <;> ext <;> simp <;> linarith

end Option2.NativeStress.HTPhaseComplete

#print axioms Option2.NativeStress.HTPhaseComplete.nZ_support
#print axioms Option2.NativeStress.HTPhaseComplete.nZ_unit
