module

public import A3Family

@[expose] public section

/-!
# The 39 literal projectors span the native Albert algebra at every unit phase

Each of the thirteen literal frames is a native Jordan frame (A3's `literal_frame`), and points of
distinct frames have trace overlap `1/3` (A3's `literalCfg_originalEquations`, cross-frame rows,
through `coordinatePairing_upperCoordinates_eq_native_trace`). Hence the centred points
`P - 1/3` of distinct frames are orthogonal for the positive trace form, each frame contributes a
two-dimensional centred plane, and with the unit (`Σ_a P_{f,a} = 1`) these give `1 + 13·2 = 27`
independent vectors in the 27-dimensional algebra.
-/

noncomputable section

namespace CKM.NativeIntrinsicTriality

open CKM.NativeFirstOrder

open NativePolynomial NativePolynomial.ConfigurationResiduals

/-- The trace form `⟪x, y⟫ = trace (x ∘ y)` as a bilinear map. -/
private def traceForm : Glennie.Albert →ₗ[ℝ] Glennie.Albert →ₗ[ℝ] ℝ :=
  Glennie.jordanLinear.compr₂ Glennie.traceLinear

private theorem traceForm_apply (x y : Glennie.Albert) :
    traceForm x y = Glennie.trace (Glennie.jordan x y) := rfl

/-- Points of distinct literal frames have trace overlap `1/3`. -/
private theorem cross_trace_lt (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (f g : Fin 13)
    (hfg : f.val < g.val) (a b : Fin 3) :
    Glennie.trace (Glennie.jordan (literalPoint ξ (framePointIndex f a))
      (literalPoint ξ (framePointIndex g b))) = 1 / 3 := by
  have hlt : framePointIndex f a < framePointIndex g b := by
    rw [Fin.lt_def, framePointIndex_val, framePointIndex_val]
    omega
  have h := (literalCfg_originalEquations ξ hξ).pair ⟨(framePointIndex f a, framePointIndex g b), hlt⟩
  change CoordinateMaps.coordinatePairing (upperCoordinates (literalPoint ξ (framePointIndex f a)))
    (upperCoordinates (literalPoint ξ (framePointIndex g b))) = _ at h
  rw [CoordinateMaps.coordinatePairing_upperCoordinates_eq_native_trace] at h
  rw [h, ite_eq_right]
  simp only [framePointIndex_val]
  omega

/-- The trace Gram matrix of the 39 literal points. -/
private theorem point_gram (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (f g : Fin 13) (a b : Fin 3) :
    traceForm (literalPoint ξ (framePointIndex f a)) (literalPoint ξ (framePointIndex g b)) =
      if f = g then (if a = b then 1 else 0) else 1 / 3 := by
  rw [traceForm_apply]
  by_cases hfg : f = g
  · subst hfg
    rw [ite_eq_left rfl]
    have hF := literal_frame ξ hξ f
    by_cases hab : a = b
    · subst hab
      rw [ite_eq_left rfl]
      have h1 := hF.idempotent a
      have h2 := hF.trace_one a
      rw [h1, h2]
    · rw [ite_eq_right hab]
      have h0 := hF.orthogonal a b hab
      rw [h0]
      exact map_zero Glennie.traceLinear
  · rw [ite_eq_right hfg]
    rcases lt_or_gt_of_ne (fun h : f.val = g.val => hfg (Fin.ext h)) with h | h
    · exact cross_trace_lt ξ hξ f g h a b
    · rw [Glennie.jordan_comm]
      exact cross_trace_lt ξ hξ g f h b a

private theorem traceForm_one_left (x : Glennie.Albert) : traceForm 1 x = Glennie.trace x := by
  rw [traceForm_apply, Glennie.jordan_unit_left]

private theorem traceForm_one_right (x : Glennie.Albert) : traceForm x 1 = Glennie.trace x := by
  rw [traceForm_apply, Glennie.jordan_unit_right]

/-- The 27 test vectors: the unit and the centred points `P_{f,a} - 1/3` for `a = 0, 1`. -/
private def testVec (ξ : Fin 4 → ℂ) : Option (Fin 13 × Fin 2) → Glennie.Albert
  | none => 1
  | some (f, a) => literalPoint ξ (framePointIndex f a.castSucc) - (1 / 3 : ℝ) • (1 : Glennie.Albert)

private theorem point_trace (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (f : Fin 13) (a : Fin 3) :
    Glennie.trace (literalPoint ξ (framePointIndex f a)) = 1 :=
  (literal_frame ξ hξ f).trace_one a

private theorem testVec_gram_some (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (f g : Fin 13)
    (a b : Fin 2) :
    traceForm (testVec ξ (some (f, a))) (testVec ξ (some (g, b))) =
      if f = g then (if a = b then 1 else 0) - 1 / 3 else 0 := by
  simp only [testVec, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, point_gram ξ hξ, traceForm_one_left, traceForm_one_right, point_trace ξ hξ,
    Glennie.trace_unit]
  have hab : (a.castSucc = b.castSucc) ↔ a = b := Fin.castSucc_inj
  by_cases hfg : f = g
  · by_cases h : a = b
    · simp only [hfg, h, ite_true]; norm_num
    · rw [ite_eq_left hfg, ite_eq_left hfg, ite_eq_right (mt hab.mp h), ite_eq_right h]; norm_num
  · rw [ite_eq_right hfg, ite_eq_right hfg]; norm_num

private theorem testVec_gram_none (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (f : Fin 13)
    (a : Fin 2) : traceForm (testVec ξ (some (f, a))) (testVec ξ none) = 0 := by
  simp only [testVec, traceForm_one_right, Glennie.trace_sub, Glennie.trace_smul,
    point_trace ξ hξ, Glennie.trace_unit]
  norm_num

private theorem testVec_linearIndependent (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    LinearIndependent ℝ (testVec ξ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ j, ∑ i, c i * traceForm (testVec ξ i) (testVec ξ j) = 0 := by
    intro j
    have := congrArg (fun x => traceForm x (testVec ξ j)) hc
    simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, map_zero, LinearMap.zero_apply] using this
  have hsome : ∀ g : Fin 13, ∀ b : Fin 2,
      c (some (g, 0)) * ((if (0 : Fin 2) = b then 1 else 0) - 1 / 3) +
        c (some (g, 1)) * ((if (1 : Fin 2) = b then 1 else 0) - 1 / 3) = 0 := by
    intro g b
    have h := key (some (g, b))
    rw [Fintype.sum_option, Fintype.sum_prod_type] at h
    simp only [Fin.sum_univ_two, testVec_gram_some ξ hξ, mul_ite, mul_zero, ite_add_ite,
      add_zero] at h
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    have h0 : traceForm (testVec ξ none) (testVec ξ (some (g, b))) = 0 := by
      rw [traceForm_apply, Glennie.jordan_comm, ← traceForm_apply]
      exact testVec_gram_none ξ hξ g b
    rw [h0, mul_zero, zero_add] at h
    exact h
  have hnone : c none = 0 := by
    have h := key none
    rw [Fintype.sum_option] at h
    simp only [testVec_gram_none ξ hξ, mul_zero, Finset.sum_const_zero, add_zero] at h
    simp only [testVec, traceForm_one_left, Glennie.trace_unit] at h
    linarith
  intro i
  rcases i with _ | ⟨g, b⟩
  · exact hnone
  · have h0 := hsome g 0
    have h1 := hsome g 1
    simp only [ite_true, show ((1 : Fin 2) = 0) = False from propext ⟨by decide, False.elim⟩,
      show ((0 : Fin 2) = 1) = False from propext ⟨by decide, False.elim⟩, ite_false] at h0 h1
    have e0 : c (some (g, 0)) = 0 := by linarith
    have e1 : c (some (g, 1)) = 0 := by linarith
    fin_cases b
    · exact e0
    · exact e1

private theorem testVec_mem_span (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Option (Fin 13 × Fin 2)) :
    testVec ξ i ∈ Submodule.span ℝ (Set.range (literalPoint ξ)) := by
  have hpt : ∀ j, literalPoint ξ j ∈ Submodule.span ℝ (Set.range (literalPoint ξ)) :=
    fun j => Submodule.subset_span ⟨j, rfl⟩
  have hone : (1 : Glennie.Albert) ∈ Submodule.span ℝ (Set.range (literalPoint ξ)) := by
    rw [← (literal_frame ξ hξ 0).sum_unit]
    exact Submodule.add_mem _ (Submodule.add_mem _ (hpt _) (hpt _)) (hpt _)
  rcases i with _ | ⟨f, a⟩
  · exact hone
  · exact Submodule.sub_mem _ (hpt _) (Submodule.smul_mem _ _ hone)

private theorem finrank_albert : Module.finrank ℝ Glennie.Albert = 27 := by
  rw [LinearEquiv.finrank_eq upperCoordinateEquiv, Module.finrank_fin_fun]

/-- The 39 literal projectors span the Albert algebra, at every unit phase. -/
theorem span_literalPoint (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Submodule.span ℝ (Set.range (literalPoint ξ)) = ⊤ := by
  have : FiniteDimensional ℝ Glennie.Albert :=
    LinearEquiv.finiteDimensional upperCoordinateEquiv.symm
  have htop := (testVec_linearIndependent ξ hξ).span_eq_top_of_card_eq_finrank
    (by rw [finrank_albert]; rfl)
  rw [eq_top_iff, ← htop, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact testVec_mem_span ξ hξ i

end CKM.NativeIntrinsicTriality

#print axioms CKM.NativeIntrinsicTriality.span_literalPoint
