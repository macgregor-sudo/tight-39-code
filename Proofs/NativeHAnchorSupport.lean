module

public import NativeHWeights
public import OriginalFAnchorRowSupport

@[expose] public section

/-!
Actual row-incidence and ambient support for every delivered native H list.
The row-support theorem is used with its original finite support sets.
All 1053 variables and all 2184 literal original half/third rows are retained.
No coefficient cancellation, anchor-column equilibrium, H-to-q, T, phase
continuation, local exhaustion or residual-distance estimate is proved here.
-/

noncomputable section

namespace Option2.NativeStress.NativeH

open ConfigurationResidualIndices AnchorRowSupport AnchorSupport

/-- A decidable inspection of the actual typed residual's point incidence. -/
def labelLocal (i : Fin 4) : FLabel → Bool
  | .inl (p, _) => decide (p.val / 3 = 0 ∨
      (1 + 3 * i.val ≤ p.val / 3 ∧ p.val / 3 ≤ 3 + 3 * i.val))
  | .inr (.inl p) => decide (p.val / 3 = 0 ∨
      (1 + 3 * i.val ≤ p.val / 3 ∧ p.val / 3 ≤ 3 + 3 * i.val))
  | .inr (.inr (.inl (f, _))) => decide (f.val = 0 ∨
      (1 + 3 * i.val ≤ f.val ∧ f.val ≤ 3 + 3 * i.val))
  | .inr (.inr (.inr pq)) => decide (
      (pq.val.1.val / 3 = 0 ∨ (1 + 3 * i.val ≤ pq.val.1.val / 3 ∧
        pq.val.1.val / 3 ≤ 3 + 3 * i.val)) ∧
      (pq.val.2.val / 3 = 0 ∨ (1 + 3 * i.val ≤ pq.val.2.val / 3 ∧
        pq.val.2.val / 3 ≤ 3 + 3 * i.val)))

theorem labelLocal_iff (i : Fin 4) (q : FLabel) :
    labelLocal i q = true ↔ LabelUsesAnchor i q := by
  rcases q with ⟨p,k⟩ | p | ⟨f,k⟩ | pq <;>
    simp only [labelLocal, decide_eq_true_eq, LabelUsesAnchor, AnchorPoint, AnchorFrame]

private theorem local0 : lambda0.all (fun e => labelLocal 0 e.label) = true := by decide
private theorem local2 : lambda2.all (fun e => labelLocal 0 e.label) = true := by decide
private theorem local1 : lambda1.all (fun e => labelLocal 0 e.label) = true := by decide
private theorem local22 : lambda22.all (fun e => labelLocal 1 e.label) = true := by decide
private theorem local14 : lambda14.all (fun e => labelLocal 1 e.label) = true := by decide
private theorem local8 : lambda8.all (fun e => labelLocal 1 e.label) = true := by decide
private theorem local4 : lambda4.all (fun e => labelLocal 2 e.label) = true := by decide
private theorem local25 : lambda25.all (fun e => labelLocal 2 e.label) = true := by decide
private theorem local11 : lambda11.all (fun e => labelLocal 2 e.label) = true := by decide
private theorem local10 : lambda10.all (fun e => labelLocal 3 e.label) = true := by decide
private theorem local5 : lambda5.all (fun e => labelLocal 3 e.label) = true := by decide
private theorem local24 : lambda24.all (fun e => labelLocal 3 e.label) = true := by decide

private theorem all_local (i : Fin 4) (a : Fin 3) :
    (rawEntries i a).all (fun e => labelLocal i e.label) = true := by
  fin_cases i <;> fin_cases a
  · exact local0
  · exact local2
  · exact local1
  · exact local22
  · exact local14
  · exact local8
  · exact local4
  · exact local25
  · exact local11
  · exact local10
  · exact local5
  · exact local24

private theorem nodup0 : (lambda0.map Entry.label).Nodup := by decide
private theorem nodup2 : (lambda2.map Entry.label).Nodup := by decide
private theorem nodup1 : (lambda1.map Entry.label).Nodup := by decide
private theorem nodup22 : (lambda22.map Entry.label).Nodup := by decide
private theorem nodup14 : (lambda14.map Entry.label).Nodup := by decide
private theorem nodup8 : (lambda8.map Entry.label).Nodup := by decide
private theorem nodup4 : (lambda4.map Entry.label).Nodup := by decide
private theorem nodup25 : (lambda25.map Entry.label).Nodup := by decide
private theorem nodup11 : (lambda11.map Entry.label).Nodup := by decide
private theorem nodup10 : (lambda10.map Entry.label).Nodup := by decide
private theorem nodup5 : (lambda5.map Entry.label).Nodup := by decide
private theorem nodup24 : (lambda24.map Entry.label).Nodup := by decide

/-- The literal raw lists contain no repeated canonical label. -/
theorem rawLabels_nodup (i : Fin 4) (a : Fin 3) :
    ((rawEntries i a).map Entry.label).Nodup := by
  fin_cases i <;> fin_cases a
  · exact nodup0
  · exact nodup2
  · exact nodup1
  · exact nodup22
  · exact nodup14
  · exact nodup8
  · exact nodup4
  · exact nodup25
  · exact nodup11
  · exact nodup10
  · exact nodup5
  · exact nodup24

/-- Signs and conjugations preserve all twelve exact list lengths. -/
theorem hEntries_length (i : Fin 4) (a : Fin 3) :
    (hEntries i a).length =
      ![![118,118,119], ![104,109,109], ![100,95,101], ![105,103,99]] i a := by
  fin_cases i <;> fin_cases a <;> rfl

/-- Canonical fNumber is injective: no duplicate numbered row is hidden. -/
theorem hEntries_rows_nodup (i : Fin 4) (a : Fin 3) :
    ((hEntries i a).map Prod.fst).Nodup := by
  have h := (rawLabels_nodup i a).map fNumber.injective
  simpa only [hEntries, List.map_map, Function.comp_def] using h

/-- Each actual emitted row belongs to the specified anchor, by typed incidence. -/
theorem hEntries_rows (i : Fin 4) (a : Fin 3) (e : Fin 2184 × Complex)
    (he : e ∈ hEntries i a) : RowUsesAnchor i e.1 := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp he
  apply (rowUsesAnchor_number i t.label).mpr
  apply (labelLocal_iff i t.label).mp
  exact (List.all_eq_true.mp (all_local i a)) t ht

private theorem sparseWeight_uses (es : List (Fin 2184 × Complex)) (i : Fin 4)
    (h : ∀ e ∈ es, RowUsesAnchor i e.1) :
    WeightsUseAnchor (sparseWeight es) i := by
  classical
  intro r hr
  by_contra hnr
  apply hr
  unfold sparseWeight
  apply List.sum_eq_zero
  intro t ht
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp ht
  have hne : e.1 ≠ r := by
    intro heq
    exact hnr (heq ▸ h e he)
  simp only [hne, ↓reduceIte]

/-- The actual twelve complex covectors satisfy the predecessor's incidence premise. -/
theorem weightsUseAnchor (i : Fin 4) (a : Fin 3) :
    WeightsUseAnchor (weightC i a) i :=
  sparseWeight_uses (hEntries i a) i (hEntries_rows i a)

/-- Strong ambient polynomial support, at every base, without cancellation. -/
theorem contractedPolynomial_vars (P : Ambient) (i : Fin 4) (a : Fin 3) :
    ∀ v ∈ (AnchorSupport.contractedPolynomial P (weightC i a)).vars,
      AnchorCoordinate i v :=
  AnchorRowSupport.contractedPolynomial_vars P (weightC i a) i (weightsUseAnchor i a)

/-- The existing quadratic-support premise is discharged for all twelve actual H's. -/
theorem hasAnchorSupport (P : Ambient) (i : Fin 4) (a : Fin 3) :
    HasAnchorSupport P (weightC i a) i :=
  AnchorRowSupport.hasAnchorSupport P (weightC i a) i (weightsUseAnchor i a)

/-- The 729 off-anchor columns vanish at every base by structural support alone. -/
theorem off_anchor_column (P : Ambient) (i : Fin 4) (a : Fin 3)
    (v : Fin 1053) (hv : ¬ AnchorCoordinate i v) :
    ∑ r : Fin 2184, weightC i a r * PolynomialJets.equationLinearMatrix
      (translatedRow P) r v = 0 :=
  AnchorRowSupport.off_anchor_column P (weightC i a) i (weightsUseAnchor i a) v hv

end Option2.NativeStress.NativeH
