module

public import NativeAnchorFixerSpecialUnitary
public import NativeAnchorFixerConverse

@[expose] public section

/-!
Full actual pointwise-fixer classification for the original canonical twelve.
The real-linear bijection preserves the actual native Jordan product. Visible
fixing is derived by native positivity, and the actual native decomposition
extends the frozen hidden right action to every input. The hidden identity
recovers the unique special-unitary multiplier. The accepted construction
supplies the reverse implication with the same actual labels and orientation.
The preceding identities supply the action on both visible and hidden sectors.
No topology, F4 quotient or global A1 headline is asserted.
First-party composition of the exact native owners and pinned Mathlib APIs.
Thanks to their contributors. “If I have seen further it is by standing on the
sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace CompactAlbert
open ActualQuartetStates
open QuadraticCertificate.ExactCKMConfiguration

private theorem inner_sub_left (x y z : Glennie.Albert) :
    Glennie.inner (x - y) z = Glennie.inner x z - Glennie.inner y z := by
  change Glennie.trace (Glennie.jordanLinear (x - y) z) = _
  rw [map_sub, LinearMap.sub_apply, Glennie.trace_sub]
  rfl

private theorem inner_sub_right (x y z : Glennie.Albert) :
    Glennie.inner x (y - z) = Glennie.inner x y - Glennie.inner x z := by
  rw [Glennie.inner_comm, inner_sub_left, Glennie.inner_comm y x, Glennie.inner_comm z x]

/-- Actual anchor fixing determines every zero-hidden native input, using
native positive definiteness rather than an assumed visible-span bridge. -/
theorem native_anchor_fixer_fixes_visible
    (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hprod : ∀ x y, f (Glennie.jordan x y) = Glennie.jordan (f x) (f y))
    (hfix : ∀ i : Fin 39, i.val < 12 → f (nativePoint i) = nativePoint i)
    (x : Glennie.Albert) (hx : (toTitsCoordinates x).2.2 = 0) : f x = x := by
  have hpair := Glennie.trace_pairing_preserved_of_jordan_equiv f hprod
  have hdvisible : hermitianMatrix (toTitsCoordinates (f x - x)) = 0 := by
    apply (actual_anchor_orthogonal_iff_visible_zero _).mp
    intro i hi
    change Glennie.inner (f x - x) (nativePoint i) = 0
    rw [inner_sub_left]
    have hp := hpair x (nativePoint i)
    rw [hfix i hi] at hp
    exact sub_eq_zero.mpr hp
  have hcross : Glennie.inner (f x - x) x = 0 := by
    change Glennie.trace (Glennie.jordan (f x - x) x) = 0
    rw [native_trace_jordan_eq_visible_pairing_of_hidden_eq_zero _ _ hx, hdvisible]
    simp
  have hnorm : Glennie.inner (f x - x) (f x - x) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, Glennie.inner_comm x (f x)]
    change Glennie.inner (f x) (f x) - Glennie.inner (f x) x -
      (Glennie.inner (f x) x - Glennie.inner x x) = 0
    have hn : Glennie.inner (f x) (f x) = Glennie.inner x x := hpair x x
    rw [inner_sub_left] at hcross
    linarith
  exact sub_eq_zero.mp ((Glennie.inner_self_eq_zero _).mp hnorm)


private theorem native_visible_hidden_decomposition (x : Glennie.Albert) :
    x = includeHermitianMatrix
        ⟨hermitianMatrix (toTitsCoordinates x), hermitianMatrix_isHermitian _⟩ +
      nativeHiddenMatrix (nativeTitsMatrixPair x).2 := by
  apply nativeTitsMatrixPair_injective
  rw [map_add, includeHermitianMatrix_pair, nativeHiddenMatrix_pair]
  apply Prod.ext <;> simp
  rfl

private theorem full_pair_of_hidden_action
    (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hprod : ∀ x y, f (Glennie.jordan x y) = Glennie.jordan (f x) (f y))
    (hfix : ∀ i : Fin 39, i.val < 12 → f (nativePoint i) = nativePoint i)
    (R : TitsComplexMatrix)
    (hhidden : ∀ B : TitsComplexMatrix,
      nativeTitsMatrixPair (f (nativeHiddenMatrix B)) = (0, B * R))
    (x : Glennie.Albert) :
    nativeTitsMatrixPair (f x) =
      ((nativeTitsMatrixPair x).1, (nativeTitsMatrixPair x).2 * R) := by
  let v := includeHermitianMatrix
    ⟨hermitianMatrix (toTitsCoordinates x), hermitianMatrix_isHermitian _⟩
  let B := (nativeTitsMatrixPair x).2
  have hvpair : nativeTitsMatrixPair v = ((nativeTitsMatrixPair x).1, 0) :=
    includeHermitianMatrix_pair _
  have hvfix : f v = v :=
    native_anchor_fixer_fixes_visible f hprod hfix v (congrArg Prod.snd hvpair)
  have hdecomp : x = v + nativeHiddenMatrix B := native_visible_hidden_decomposition x
  have hfx : f x = v + f (nativeHiddenMatrix B) := by
    calc
      f x = f (v + nativeHiddenMatrix B) := congrArg f hdecomp
      _ = f v + f (nativeHiddenMatrix B) := map_add f _ _
      _ = v + f (nativeHiddenMatrix B) := by rw [hvfix]
  rw [hfx, map_add, hvpair, hhidden]
  simp only [Prod.mk_add_mk, add_zero, zero_add]
  rfl

/-- A real-linear actual native Jordan automorphism fixes the original first
twelve canonical points exactly when its full native matrix-pair action is
right multiplication by a unique determinant-one right unitary. No trace,
metric, visible-fixing or full-action premise is added. -/
theorem native_anchor_fixer_classification
    (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hprod : ∀ x y, f (Glennie.jordan x y) = Glennie.jordan (f x) (f y)) :
    (∀ i : Fin 39, i.val < 12 → f (nativePoint i) = nativePoint i) ↔
      ∃! R : TitsComplexMatrix,
        R * R.conjTranspose = (1 : TitsComplexMatrix) ∧ R.det = 1 ∧
        ∀ x : Glennie.Albert,
          nativeTitsMatrixPair (f x) =
            ((nativeTitsMatrixPair x).1, (nativeTitsMatrixPair x).2 * R) := by
  constructor
  · intro hfix
    obtain ⟨R, hR, hhidden⟩ := native_anchor_fixer_right_action f hprod hfix
    have hsu := native_anchor_fixer_multiplier_specialUnitary f hprod hfix
    change (nativeTitsMatrixPair (f (nativeHiddenMatrix 1))).2 *
        (nativeTitsMatrixPair (f (nativeHiddenMatrix 1))).2.conjTranspose = 1 ∧
      (nativeTitsMatrixPair (f (nativeHiddenMatrix 1))).2.det = 1 at hsu
    rw [← hR] at hsu
    refine ⟨R, ⟨hsu.1, hsu.2, full_pair_of_hidden_action f hprod hfix R hhidden⟩, ?_⟩
    intro S hS
    have hSidentity := congrArg Prod.snd (hS.2.2 (nativeHiddenMatrix 1))
    simp only [nativeHiddenMatrix_pair, one_mul] at hSidentity
    exact hSidentity.symm.trans hR.symm
  · rintro ⟨R, hR, _⟩
    obtain ⟨g, _, hgfix, hgpair⟩ := native_anchor_fixer_converse R hR.1 hR.2.1
    intro i hi
    have hfg : f (nativePoint i) = g (nativePoint i) := by
      apply nativeTitsMatrixPair_injective
      rw [hR.2.2, hgpair]
    exact hfg.trans (hgfix i hi)

end CompactAlbert
