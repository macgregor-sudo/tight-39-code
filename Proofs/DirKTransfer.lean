module

public import DirKCheck

@[expose] public section

/-! Symbolic transfer of the kernel checks of DirKCheck to the Q12 statements. First-party. -/

set_option Elab.async false
namespace Option2.NativeStress.HTPhaseComplete
open Option2.NativeStress.BookHT Option2.NativeStress.BookHT.TangentCoordinates

/-! ## Transfer to Q12 -/

theorem gToQ12_apply (z : GaussianInt) : gToQ12 z = (z.re : Q12) + (z.im : Q12) * Q12.I := by
  simp [gToQ12]

theorem gToQ12_gaussI : gToQ12 gaussI = Q12.I := by
  rw [gToQ12_apply]; simp [gaussI]

theorem litAt_eq_litZ (l : List KLit) (hl : ∀ e ∈ l, entryOk e = true) (k c : Fin 27) :
    litAt l k c = ((litZ l k c : ℤ) : Q12) := by
  unfold litAt litZ
  cases hf : findLit l k c with
  | none => simp
  | some e =>
    have he := hl e (List.mem_of_find?_eq_some hf)
    obtain ⟨r, row, A, B, C, D', N⟩ := e
    simp only [entryOk, Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨⟨⟨hB, hC⟩, hD⟩, hN⟩ := he
    subst hB hC hD hN
    simp only [Option.map_some, Option.getD_some, litVal]
    ext <;> simp [Q12.lit, Rat.mkRat_eq_div]

theorem kPairOf_mem {j : Fin 24} {pr : ℕ × ℕ × ℕ × List KLit × List KLit}
    (h : kPairOf j = some pr) : pr ∈ kPairs := List.mem_of_find?_eq_some h

theorem kPairs_entries {pr : ℕ × ℕ × ℕ × List KLit × List KLit} (h : pr ∈ kPairs) :
    (∀ e ∈ pr.2.2.2.1, entryOk e = true) ∧ (∀ e ∈ pr.2.2.2.2, entryOk e = true) := by
  have hw := (List.all_eq_true.mp kData_wellFormed.1) pr h
  simp only [Bool.and_eq_true, List.all_eq_true] at hw
  exact ⟨hw.1.1.1, hw.1.1.2⟩

/-- The Q12 literal reading of the JSON equals half the Gaussian-integer reading. -/
theorem kMat_eq_kZ (j : Fin 24) (k c : Fin 27) : kMat j k c = kHalf * gToQ12 (kZ j k c) := by
  unfold kMat kZ
  cases h : kPairOf j with
  | none => simp
  | some pr =>
    obtain ⟨h1, h2⟩ := kPairs_entries (kPairOf_mem h)
    simp only [litAt_eq_litZ _ h1, litAt_eq_litZ _ h2]
    split_ifs <;> rw [gToQ12_apply] <;> push_cast <;> ring

theorem kMat_eq_q12Op_indep {j : Fin 24} (hj : j ∈ indepList) (c k : Fin 27) :
    kMat j k c = q12Op (eigenIndex j) (Pi.single c 1) k := by
  have hs : (Pi.single c (1 : Q12) : Fin 27 → Q12) = fun m => gToQ12 (ebZ c m) := by
    funext m
    by_cases hm : m = c
    · subst hm; simp [ebZ]
    · have : m.val ≠ c.val := fun h => hm (Fin.ext h)
      simp [ebZ, hm, this]
  have hz := zCheck_indep j hj
  simp only [zCheck, List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] at hz
  rw [q12Op_eq_opG, opG_smul, hs, ← gToQ12_gaussI, opG_map, hz c k, kMat_eq_kZ]
  rfl

theorem gToQ12_star (z : GaussianInt) : gToQ12 (star z) = Q12.conj (gToQ12 z) := by
  rw [gToQ12_apply, gToQ12_apply, map_add, map_mul, map_intCast, map_intCast]
  have hI : Q12.conj Q12.I = -Q12.I := by decide +kernel
  rw [hI]
  simp only [Zsqrtd.re_star, Zsqrtd.im_star, Int.cast_neg]
  ring

theorem kZ_bar (j : Fin 24) (k c : Fin 27) :
    kZ (Dictionary.coordinateBar j) k c = -star (kZ j k c) := by
  have hb : ∀ j ∈ indepList, ∀ k c : Fin 27,
      kZ (Dictionary.coordinateBar j) k c = ⟨-(kZ j k c).re, (kZ j k c).im⟩ := by
    intro j hj
    have h := barCheck_indep j hj
    simpa only [barCheck, List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] using h
  have hs (z : GaussianInt) : (⟨-z.re, z.im⟩ : GaussianInt) = -star z := by
    ext <;> simp [Zsqrtd.re_star, Zsqrtd.im_star]
  rcases indep_or_bar j with h | h
  · rw [hb j h k c, hs]
  · have h2 := hb _ h k c
    rw [hs] at h2
    rw [Dictionary.coordinateBar_involutive j] at h2
    rw [h2, star_neg, star_star, neg_neg]

/-- Real structure of the JSON operators: `K_{j̄} = −conj K_j` with the accepted coordinate bar. -/
theorem kMat_bar (j : Fin 24) (k c : Fin 27) :
    kMat (Dictionary.coordinateBar j) k c = -Q12.conj (kMat j k c) := by
  have hh : Q12.conj kHalf = kHalf := by decide +kernel
  rw [kMat_eq_kZ, kMat_eq_kZ, kZ_bar, map_neg, gToQ12_star, map_mul, hh]
  ring

/-- Accepted conjugation symmetry of the sheet operator on conjugation-fixed inputs. -/
theorem q12Op_bar (b : Fin 24) (x : Fin 27 → Q12) (hx : ∀ m, Q12.conj (x m) = x m) (k : Fin 27) :
    q12Op (basisBar b) x k = -Q12.conj (q12Op b x k) := by
  have hs := (basisBar_sheet_root b).1
  have hr := (basisBar_sheet_root b).2
  unfold q12Op
  rw [hs, hr]
  let x' := q12SheetInverse (d6Sheet b) x
  have hx' : (fun j => Q12.conj (x' j)) = x' := by
    change (fun j => Q12.conj (q12SheetInverse (d6Sheet b) x j)) = _
    rw [← q12SheetInverse_conj]
    congr 1
    funext j
    exact hx j
  have hroot : q12RootCoordinates
      (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).2
      (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).1 x' =
      -(fun j => Q12.conj (q12RootCoordinates
        (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).1
        (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).2 x' j)) := by
    funext j
    have h := q12RootCoordinates_conj
      (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).1
      (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).2 x' j
    rw [hx'] at h
    exact h
  change q12SheetTransport (d6Sheet b) (q12RootCoordinates
    (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).2
    (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).1 x') k = _
  rw [hroot, q12SheetTransport_neg, q12SheetTransport_conj]
  rfl

theorem single_conj (c m : Fin 27) :
    Q12.conj ((Pi.single c (1 : Q12) : Fin 27 → Q12) m) = (Pi.single c (1 : Q12) : Fin 27 → Q12) m := by
  by_cases hm : m = c
  · subst hm; rw [Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne hm, map_zero]

/-- JSON = Lean: every entry of every fixed operator equals the accepted Q12 sheet operator. -/
theorem kMat_eq_q12Op (j : Fin 24) (c k : Fin 27) :
    kMat j k c = q12Op (eigenIndex j) (Pi.single c 1) k := by
  rcases indep_or_bar j with h | h
  · exact kMat_eq_q12Op_indep h c k
  · obtain ⟨j0, rfl⟩ : ∃ j0, j = Dictionary.coordinateBar j0 :=
      ⟨Dictionary.coordinateBar j, (Dictionary.coordinateBar_involutive j).symm⟩
    rw [Dictionary.coordinateBar_involutive j0] at h
    rw [kMat_bar, kMat_eq_q12Op_indep h, eigenIndex_bar', q12Op_bar _ _ (single_conj c)]

end Option2.NativeStress.HTPhaseComplete
open Option2.NativeStress.HTPhaseComplete
#print axioms kData_wellFormed
#print axioms kMat_eq_kZ
#print axioms kMat_eq_q12Op
#print axioms kMat_bar
