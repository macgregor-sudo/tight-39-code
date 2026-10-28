module

public import NativeConfigurationEvaluation
public import NativeConfigurationIdealEquality

@[expose] public section

/-!
# Configurations of 39 native points and the G/F row equations (brief C5)

`Cfg S := Fin 39 → Fin 27 → S`; `pack C : Fin 1053 → S` is the point-first packing with
`pointValues (pack C) i = C i`.  `ConfigEquations h t C` are the native Jordan equations
(idempotency, trace one, within-frame products zero, frame sums = unit, cross-frame pairing = t).
Theorem: they force every numbered G row (`valueRow`, `gRow`) and every F row to vanish at `pack C`.
Automorphisms (product/unit/trace/pairing-preserving additive maps) applied pointwise preserve
`ConfigEquations`.  First-party composition over the imported native definitions.
-/

namespace TitsS

open NativePolynomial.CoordinateMaps NativePolynomial.ConfigurationResiduals
open NativePolynomial.ConfigurationResiduals.Evaluation
open NativePolynomial.ConfigurationResiduals.MixedCoefficients ConfigurationResidualIndices

variable {S : Type*} [CommRing S]

/-- A configuration: 39 native points. -/
abbrev Cfg (S : Type*) := Fin 39 → Fin 27 → S

/-- Point-first packing, matching `variableIndex i k = 27 i + k`. -/
def pack (C : Cfg S) : Fin 1053 → S :=
  fun v => C ⟨v.val / 27, by omega⟩ ⟨v.val % 27, by omega⟩

omit [CommRing S] in
theorem pack_variableIndex (C : Cfg S) (i : Fin 39) (k : Fin 27) :
    pack C (variableIndex i k) = C i k := by
  unfold pack
  have h1 : (variableIndex i k).val / 27 = i.val := by rw [variableIndex_val]; omega
  have h2 : (variableIndex i k).val % 27 = k.val := by rw [variableIndex_val]; omega
  have e1 : (⟨(variableIndex i k).val / 27, by omega⟩ : Fin 39) = i := Fin.ext h1
  have e2 : (⟨(variableIndex i k).val % 27, by omega⟩ : Fin 27) = k := Fin.ext h2
  rw [e1, e2]

omit [CommRing S] in
theorem pointValues_pack (C : Cfg S) (i : Fin 39) : pointValues (pack C) i = C i :=
  funext fun k => pack_variableIndex C i k

omit [CommRing S] in
theorem pack_eq (C : Cfg S) (v : Fin 1053) :
    pack C v = C ⟨v.val / 27, by omega⟩ ⟨v.val % 27, by omega⟩ := rfl

/-- The native Jordan equations of a 13-frame configuration. -/
structure ConfigEquations (h t : S) (C : Cfg S) : Prop where
  idem : ∀ i, coordinateProduct h (C i) (C i) = C i
  trace : ∀ i, coordinateTrace (C i) = 1
  within : ∀ (f : Fin 13) (a b : Fin 3), a ≠ b →
    coordinateProduct h (C (framePointIndex f a)) (C (framePointIndex f b)) = 0
  sum : ∀ f : Fin 13,
    C (framePointIndex f 0) + C (framePointIndex f 1) + C (framePointIndex f 2) = coordinateUnit
  cross : ∀ (f g : Fin 13), f ≠ g → ∀ a b : Fin 3,
    coordinatePairing (C (framePointIndex f a)) (C (framePointIndex g b)) = t

variable {h t : S} {C : Cfg S}

theorem valueResidual_pack_eq_zero (hC : ConfigEquations h t C) (q : GLabel) :
    valueResidual h t (pack C) q = 0 := by
  rcases q with ⟨i, k⟩ | ⟨⟨f, s⟩, k⟩ | ⟨f, k⟩ | ⟨fg, a, b⟩
  · simp only [valueResidual, pointValues_pack]
    rw [hC.idem i]
    exact sub_self _
  · simp only [valueResidual, pointValues_pack]
    have hne : (withinPair s).val.1 ≠ (withinPair s).val.2 := ne_of_lt (withinPair s).property
    rw [hC.within f _ _ hne]
    rfl
  · simp only [valueResidual, pointValues_pack, Fin.sum_univ_three]
    have := congrFun (hC.sum f) k
    simp only [Pi.add_apply] at this
    rw [this, sub_self]
  · simp only [valueResidual, pointValues_pack]
    have hne : fg.val.1 ≠ fg.val.2 := ne_of_lt fg.property
    rw [hC.cross _ _ hne]
    exact sub_self _

theorem valueRow_pack_eq_zero (hC : ConfigEquations h t C) (r : Fin 3159) :
    valueRow h t (pack C) r = 0 :=
  valueResidual_pack_eq_zero hC _

/-- Every numbered G row vanishes at a configuration satisfying the native equations. -/
theorem eval_gRow_pack (hC : ConfigEquations h t C) (r : Fin 3159) :
    MvPolynomial.eval (pack C) (gRow h t r) = 0 := by
  rw [gRow_eval]
  exact valueRow_pack_eq_zero hC r

/-- Every numbered F row vanishes too (F ⊆ span G, `fRow_mem_gSpan`). -/
theorem eval_fRow_pack (h2 : (2 : S) * h = 1) (t3 : (3 : S) * t = 1)
    (hC : ConfigEquations h t C) (r : Fin 2184) :
    MvPolynomial.eval (pack C) (fRow h t r) = 0 := by
  have hmem := fRow_mem_gSpan h t h2 t3 r
  have hker : Ideal.span (Set.range (gRow h t)) ≤
      RingHom.ker (MvPolynomial.eval (pack C)) := by
    rw [Ideal.span_le]
    rintro _ ⟨r, rfl⟩
    exact RingHom.mem_ker.mpr (eval_gRow_pack hC r)
  exact RingHom.mem_ker.mp (hker hmem)

/-! ### Automorphisms preserve the equations -/

/-- An additive map preserving product, unit, trace and pairing. -/
structure IsAut (h : S) (φ : (Fin 27 → S) → (Fin 27 → S)) : Prop where
  map_add : ∀ x y, φ (x + y) = φ x + φ y
  map_zero : φ 0 = 0
  map_prod : ∀ x y, φ (coordinateProduct h x y) = coordinateProduct h (φ x) (φ y)
  map_unit : φ coordinateUnit = coordinateUnit
  map_trace : ∀ x, coordinateTrace (φ x) = coordinateTrace x
  map_pairing : ∀ x y, coordinatePairing (φ x) (φ y) = coordinatePairing x y

theorem IsAut.comp {φ ψ : (Fin 27 → S) → (Fin 27 → S)} (hφ : IsAut h φ) (hψ : IsAut h ψ) :
    IsAut h (φ ∘ ψ) where
  map_add x y := by simp [hψ.map_add, hφ.map_add]
  map_zero := by simp [hψ.map_zero, hφ.map_zero]
  map_prod x y := by simp [hψ.map_prod, hφ.map_prod]
  map_unit := by simp [hψ.map_unit, hφ.map_unit]
  map_trace x := by simp [hψ.map_trace, hφ.map_trace]
  map_pairing x y := by simp [hψ.map_pairing, hφ.map_pairing]

theorem IsAut.id : IsAut h (fun x : Fin 27 → S => x) where
  map_add _ _ := rfl
  map_zero := rfl
  map_prod _ _ := rfl
  map_unit := rfl
  map_trace _ := rfl
  map_pairing _ _ := rfl

theorem ConfigEquations.map {φ : (Fin 27 → S) → (Fin 27 → S)} (hφ : IsAut h φ)
    (hC : ConfigEquations h t C) : ConfigEquations h t (fun i => φ (C i)) where
  idem i := by rw [← hφ.map_prod, hC.idem]
  trace i := by rw [hφ.map_trace, hC.trace]
  within f a b hab := by rw [← hφ.map_prod, hC.within f a b hab, hφ.map_zero]
  sum f := by rw [← hφ.map_add, ← hφ.map_add, hC.sum, hφ.map_unit]
  cross f g hfg a b := by rw [hφ.map_pairing, hC.cross f g hfg]

/-- Applying automorphisms point by point (possibly different per point is NOT allowed here;
this is the diagonal action). -/
theorem ConfigEquations.map_pointwise {φ : (Fin 27 → S) → (Fin 27 → S)} (hφ : IsAut h φ)
    (hC : ConfigEquations h t C) : ConfigEquations h t (φ ∘ C) :=
  hC.map hφ

end TitsS

#print axioms TitsS.eval_gRow_pack
#print axioms TitsS.eval_fRow_pack
#print axioms TitsS.ConfigEquations.map
#print axioms TitsS.pointValues_pack
