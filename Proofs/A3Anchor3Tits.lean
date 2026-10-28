module

public import A3Interfaces

@[expose] public section

/-!
# Anchor H3: `T₃⁻¹` in Tits coordinates

`transportTinv 2` is a signed coordinate permutation; in Tits coordinates `(d, c, B)` it sends every
complex entry to `±` itself or `±` its conjugate (`tits3`).
-/

noncomputable section

namespace CKM.NativeFirstOrder

namespace Anchor3

open CompactAlbert NativePolynomial

theorem T3pinv_tbl : TitsS.Transport.T3pinv = (![0, 1, 2, 9, 10, 7, 8, 5, 6, 3, 4, 13, 14, 11, 12,
    17, 18, 15, 16, 23, 24, 25, 26, 19, 20, 21, 22] : Fin 27 → Fin 27) := by decide

theorem T3si_tbl : TitsS.Transport.T3si = (![1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1, 1, -1, -1, -1, -1,
    1, 1, 1, 1, 1, -1, -1, 1, -1, -1, 1] : Fin 27 → ℤ) := by decide

theorem upperCoordinates_signedTransport (p : Fin 27 → Fin 27) (s : Fin 27 → ℤ) (x : Glennie.Albert)
    (k : Fin 27) : upperCoordinates (signedTransport p s x) k = (s k : ℝ) * upperCoordinates x (p k) := by
  change upperCoordinateEquiv (upperCoordinateEquiv.symm _) k = _
  rw [LinearEquiv.apply_symm_apply]
  simp [upperCoordinateEquiv, smul_eq_mul]

/-- `T₃⁻¹` in Tits coordinates. -/
def tits3 (q : TitsCoordinates) : TitsCoordinates :=
  (q.1, ![-star (q.2.2 0 1), star (q.2.2 1 0), star (q.2.2 2 2)],
    !![-star (q.2.2 0 2), -q.2.1 0, -q.2.2 0 0;
      -q.2.1 1, -q.2.2 1 2, star (q.2.2 1 1);
      q.2.2 2 1, -star (q.2.2 2 0), -q.2.1 2])

theorem transportTinv_two_fromTits (q : TitsCoordinates) :
    transportTinv 2 (fromTitsCoordinates q) = fromTitsCoordinates (tits3 q) := by
  apply upperCoordinateEquiv.injective
  funext k
  change upperCoordinates (signedTransport _ _ _) k = upperCoordinates _ k
  rw [upperCoordinates_signedTransport, T3pinv_tbl, T3si_tbl]
  fin_cases k <;>
    simp [upperCoordinates, fromTitsCoordinates, octonionFromTitsRow, tits3, Glennie.octConj]

end Anchor3

end CKM.NativeFirstOrder
