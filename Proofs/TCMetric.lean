module

public import TCBound

@[expose] public section

/-!
# A7: the native chordal metric 

For pure points `⟨p - q, p - q⟩ = 2 - 2⟨p, q⟩`, so `ρ(p, q) = sqrt (1 - ⟨p, q⟩)` (Cohn–Kumar–Minton
§2.1, printed page 5, normalization), and `⟨p, q⟩ ≤ 1/3 ↔ ρ(p, q) ≥ sqrt (2/3)`. The coordinate
sup norm on `Fin 27 → ℝ` plays no role.
-/

noncomputable section

namespace CKM.NativeTightCode

open Glennie

theorem chordalDist_eq {p q : Albert} (hp : IsPure p) (hq : IsPure q) :
    chordalDist p q = Real.sqrt (1 - inner p q) := by
  unfold chordalDist
  congr 1
  rw [CKM.NativeDerivationTriality.Reuse.inner_sub_left,
    CKM.NativeDerivationTriality.Reuse.inner_sub_right,
    CKM.NativeDerivationTriality.Reuse.inner_sub_right,
    inner_self_of_pure hp, inner_self_of_pure hq, Glennie.inner_comm q p]
  ring

theorem overlap_le_iff_chordalDist {p q : Albert} (hp : IsPure p) (hq : IsPure q) :
    inner p q ≤ 1 / 3 ↔ Real.sqrt (2 / 3) ≤ chordalDist p q := by
  rw [chordalDist_eq hp hq, Real.sqrt_le_sqrt_iff' (by norm_num : (0 : ℝ) < 2 / 3)]
  constructor <;> intro h <;> linarith

/-- The code bound in metric form. -/
theorem card_le_39_of_chordalDist {N : ℕ} (P : Fin N → Albert) (hpure : ∀ i, IsPure (P i))
    (hd : ∀ i j, i ≠ j → Real.sqrt (2 / 3) ≤ chordalDist (P i) (P j)) : N ≤ 39 := by
  exact card_le_39 P hpure fun i j hij =>
    (overlap_le_iff_chordalDist (hpure i) (hpure j)).mpr (hd i j hij)

#print axioms chordalDist_eq
#print axioms overlap_le_iff_chordalDist
#print axioms card_le_39_of_chordalDist

end CKM.NativeTightCode
