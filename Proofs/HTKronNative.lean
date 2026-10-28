module

public import HTKronExactness
public import NativeHBookQuadratic
public import NativeHQuadraticVariationConsumer
public import NativeTResidualQuadratic

@[expose] public section

/-!
# Complex interpretation: native and Book H/T components

First-party code. Over `ℂ` (via `toC`) the quadratic forms
`engR`, `bookR` are the accepted native homogeneous forms and the accepted Book components, each
multiplied by the nonzero literal scale `fullScale d = 2 d 384540²`. With `component_identity`
this gives, from the kernel facts `hValue i a = hBookValue i a` / `tValue i a = tBookValue i a`
and the bound checks, the two target identities through the accepted bridges
`native_H_quadratic_variation` and `native_T_quadratic_variation`.
-/

set_option autoImplicit false

noncomputable section

namespace Option2.NativeStress.HTRouteKron

open scoped BigOperators
open QuarticCertificate.RowBridge BookHT.TangentCoordinates BookHT.Dictionary
open ConfigurationResidualIndices

lemma toC_sparseZ (es : List Entry) (u : Fin 1053) :
    toC (sparseZ es u.val) = (denominator : ℂ) * sparseValue es u := by
  induction es with
  | nil => simp [sparseZ_nil, sparseValue]
  | cons e es ih =>
      rw [sparseZ_cons, map_add, ih, sparseValue, mul_add]
      congr 1
      by_cases h : u = e.1
      · rw [if_pos (by rw [h]), if_pos h, toC_ofCoeff]
      · rw [if_neg (fun h' => h (Fin.ext h'.symm)), if_neg h, map_zero, mul_zero]

lemma ptR_toC (y : Fin 24 → ℂ) : ptR toC y = fun u => (denominator : ℂ) * V y u := by
  funext u
  have hV : V y u = ∑ j, y j * eigenColumn j u := rfl
  simp only [ptR, colZ, toC_sparseZ]
  rw [hV, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  simp only [eigenColumn, d6Column]
  ring

lemma quadraticValue_scale (a c : ℂ) (l : List (Fin 1053 × Fin 1053 × ℤ)) (x : Fin 1053 → ℂ) :
    quadraticValue a l (fun u => c * x u) = a * c ^ 2 * quadraticValue 1 l x := by
  induction l with
  | nil => simp [quadraticValue]
  | cons t l ih =>
      simp only [quadraticValue, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

lemma toC_weight (d : ℕ) (s : NativeH.HSpec) (e : NativeH.Entry)
    (hd : e.coefficient.denominator ∣ d) :
    toC (weight d s e) = (2 * d : ℂ) * quadraticScale (1/2 : ℂ) (labelShape e.label) *
      NativeH.orientedValue s e.coefficient := by
  unfold weight
  rw [toC_smul, toC_orient]
  obtain ⟨m, hm⟩ := hd
  have hpos := e.coefficient.denominator_pos
  have hdiv : d / e.coefficient.denominator = m := by
    rw [hm, Nat.mul_div_cancel_left _ hpos]
  rw [hdiv, hm]
  unfold quadraticScale
  cases (labelShape e.label).halfScaled <;> simp <;> ring

lemma engR_toC (d : ℕ) (s : NativeH.HSpec) (es : List NativeH.Entry)
    (hd : ∀ e ∈ es, e.coefficient.denominator ∣ d) (y : Fin 24 → ℂ) :
    engR toC d s es y = (fullScale d : ℂ) * (es.map fun e => NativeH.orientedValue s e.coefficient *
      quadraticValue (quadraticScale (1/2 : ℂ) (labelShape e.label))
        (labelShape e.label).quadratic (V y)).sum := by
  unfold engR
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro e he
  rw [toC_weight d s e (hd e he), ptR_toC, quadraticValue_scale]
  have hq : quadraticValue (quadraticScale (1/2 : ℂ) (labelShape e.label))
      (labelShape e.label).quadratic (V y) = quadraticScale (1/2 : ℂ) (labelShape e.label) *
        quadraticValue 1 (labelShape e.label).quadratic (V y) := by
    have := quadraticValue_scale (quadraticScale (1/2 : ℂ) (labelShape e.label)) 1
      (labelShape e.label).quadratic (V y)
    simpa using this
  rw [hq]
  unfold fullScale
  push_cast
  ring

lemma bookR_scale (sc : ℤ) (l : List (Fin 24 × Fin 24 × ℤ)) (y : Fin 24 → ℂ) :
    bookR sc l y = (sc : ℂ) * (l.map fun t => (t.2.2 : ℂ) * (y t.1 * y t.2.1)).sum := by
  unfold bookR
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  push_cast
  ring

lemma denLcm_pos (es : List NativeH.Entry) : 0 < denLcm es :=
  NativeH.Reproduction.denominator_fold_pos es

lemma denLcm_dvd (es : List NativeH.Entry) : ∀ e ∈ es, e.coefficient.denominator ∣ denLcm es :=
  NativeH.Reproduction.denominator_dvd_fold es

lemma fullScale_ne_zero (es : List NativeH.Entry) : (fullScale (denLcm es) : ℂ) ≠ 0 := by
  have := denLcm_pos es
  unfold fullScale
  have h2 : (denominator : ℕ) ≠ 0 := by decide
  exact_mod_cast (by positivity : 2 * denLcm es * denominator * denominator ≠ 0)

/-! ## H -/

lemma hBook_sum (i : Fin 4) (a : Fin 3) (z : BookHT.Blocks) :
    ((hBook i a).map fun t => (t.2.2 : ℂ) * (realCoordinates z t.1 * realCoordinates z t.2.1)).sum =
      (BookHT.H z i).ofLp a := by
  rw [← NativeH.Reproduction.bookTerms_evaluate]
  unfold hBook NativeH.Reproduction.bookTerms
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def,
    NativeH.Reproduction.pairWeight_pairKey]
  apply Finset.sum_congr rfl; intro k _
  cases (NativeH.hSpec i a).negated <;> simp [map_intCast, map_neg]

theorem h_component (i : Fin 4) (a : Fin 3)
    (hs : ∀ j, (d6Entries (eigenIndex j)).Pairwise (fun e f => e.1.val < f.1.val))
    (hsid : ∀ j l j' l' : Fin 24, j ≤ l → j' ≤ l' → gol j + gol l = gol j' + gol l' →
      j = j' ∧ l = l')
    (hval : hValue i a = hBookValue i a)
    (hB : 2 * (BE (denLcm (NativeH.rawEntries i a)) (NativeH.hSpec i a) (NativeH.rawEntries i a) +
      BB (fullScale (denLcm (NativeH.rawEntries i a))) (hBook i a)) < 2 ^ width)
    (z : BookHT.Blocks) :
    NativeH.Reproduction.homogeneousH i a (V (realCoordinates z)) = (BookHT.H z i).ofLp a := by
  have key := component_identity _ _ _ _ _ hs hsid hval hB toC (realCoordinates z)
  rw [engR_toC _ _ _ (denLcm_dvd _), bookR_scale, hBook_sum] at key
  rw [NativeH.Reproduction.homogeneousH_sparse]
  have hne := fullScale_ne_zero (NativeH.rawEntries i a)
  simp only [Int.cast_natCast] at key
  exact mul_left_cancel₀ hne key

/-- First target identity, for one component. -/
theorem h_target (i : Fin 4) (a : Fin 3)
    (hs : ∀ j, (d6Entries (eigenIndex j)).Pairwise (fun e f => e.1.val < f.1.val))
    (hsid : ∀ j l j' l' : Fin 24, j ≤ l → j' ≤ l' → gol j + gol l = gol j' + gol l' →
      j = j' ∧ l = l')
    (hval : hValue i a = hBookValue i a)
    (hB : 2 * (BE (denLcm (NativeH.rawEntries i a)) (NativeH.hSpec i a) (NativeH.rawEntries i a) +
      BB (fullScale (denLcm (NativeH.rawEntries i a))) (hBook i a)) < 2 ^ width)
    (z : BookHT.Blocks) :
    (NativeH.residualContraction
        (Option2.NativeStress.originalF (Option2.BookNativeBase.bookBase + realV z)) i).ofLp a =
      (BookHT.H z i).ofLp a := by
  rw [NativeH.Reproduction.native_H_quadratic_variation,
    NativeH.Reproduction.nativeHQuadraticAlongRealV, WithLp.ofLp_toLp]
  exact h_component i a hs hsid hval hB z

/-! ## T -/

lemma tBook_sum (i : Fin 4) (a : Fin 3) (z : BookHT.Blocks) :
    ((tBook i a).map fun t => (t.2.2 : ℂ) * (realCoordinates z t.1 * realCoordinates z t.2.1)).sum =
      (BookHT.T z i).ofLp a := by
  rw [← selectedT_eq_Book]
  unfold tBook
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, Fin.sum_univ_three, quadric,
    termPolynomial, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  ring

lemma homogeneousT_entries (i : Fin 4) (a : Fin 3) (x : Fin 1053 → ℂ) :
    NativeT.Reproduction.homogeneousT i a x =
      ((NativeT.rawEntries i a).map fun e => NativeH.orientedValue (NativeT.tSpec i a) e.coefficient *
        quadraticValue (quadraticScale (1/2 : ℂ) (labelShape e.label))
          (labelShape e.label).quadratic x).sum := by
  rw [NativeT.Reproduction.homogeneousT_sparse]
  unfold NativeT.entries
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, quadraticPartValue, quadTable, rowShape,
    Equiv.symm_apply_apply]
  congr 1

theorem t_component (i : Fin 4) (a : Fin 3)
    (hs : ∀ j, (d6Entries (eigenIndex j)).Pairwise (fun e f => e.1.val < f.1.val))
    (hsid : ∀ j l j' l' : Fin 24, j ≤ l → j' ≤ l' → gol j + gol l = gol j' + gol l' →
      j = j' ∧ l = l')
    (hval : tValue i a = tBookValue i a)
    (hB : 2 * (BE (denLcm (NativeT.rawEntries i a)) (NativeT.tSpec i a) (NativeT.rawEntries i a) +
      BB (fullScale (denLcm (NativeT.rawEntries i a))) (tBook i a)) < 2 ^ width)
    (z : BookHT.Blocks) :
    NativeT.Reproduction.homogeneousT i a (V (realCoordinates z)) = (BookHT.T z i).ofLp a := by
  have key := component_identity _ _ _ _ _ hs hsid hval hB toC (realCoordinates z)
  rw [engR_toC _ _ _ (denLcm_dvd _), bookR_scale, tBook_sum] at key
  rw [homogeneousT_entries]
  have hne := fullScale_ne_zero (NativeT.rawEntries i a)
  simp only [Int.cast_natCast] at key
  exact mul_left_cancel₀ hne key

/-- Second target identity, for one component. -/
theorem t_target (i : Fin 4) (a : Fin 3)
    (hs : ∀ j, (d6Entries (eigenIndex j)).Pairwise (fun e f => e.1.val < f.1.val))
    (hsid : ∀ j l j' l' : Fin 24, j ≤ l → j' ≤ l' → gol j + gol l = gol j' + gol l' →
      j = j' ∧ l = l')
    (hval : tValue i a = tBookValue i a)
    (hB : 2 * (BE (denLcm (NativeT.rawEntries i a)) (NativeT.tSpec i a) (NativeT.rawEntries i a) +
      BB (fullScale (denLcm (NativeT.rawEntries i a))) (tBook i a)) < 2 ^ width)
    (z : BookHT.Blocks) :
    (NativeT.Reproduction.residualT
        (Option2.NativeStress.originalF (Option2.BookNativeBase.bookBase + realV z)) i).ofLp a =
      (BookHT.T z i).ofLp a := by
  rw [NativeT.Reproduction.native_T_quadratic_variation,
    NativeT.Reproduction.nativeTQuadraticAlongRealV, WithLp.ofLp_toLp]
  exact t_component i a hs hsid hval hB z

end Option2.NativeStress.HTRouteKron

end
