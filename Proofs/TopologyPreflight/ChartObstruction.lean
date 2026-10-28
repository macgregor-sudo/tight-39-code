module

public import TopologyPreflight.LocalTopology

@[expose] public section

/-!
Generic local-chart obstruction wrappers. These consume open patches and
continuous injective sheets supplied by a caller; they introduce no native
configuration, orbit action, quotient, or manifold declaration.
-/

namespace TopologyReuse

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- If `O : Set α` is open and `S : Set O` is open in the subtype topology,
    then `(Subtype.val : O → α) '' S` is open in `α`. -/
theorem isOpen_subtype_val_image {α : Type*} [TopologicalSpace α]
    {O : Set α} (hO : IsOpen O) {S : Set O} (hS : IsOpen S) :
    IsOpen ((Subtype.val : O → α) '' S) := by
  obtain ⟨T, hT, rfl⟩ := isOpen_induced_iff.mp hS
  have heq : (Subtype.val : O → α) '' (Subtype.val ⁻¹' T) = T ∩ O := by
    ext y
    constructor
    · rintro ⟨⟨z, hzO⟩, hzT, rfl⟩
      exact ⟨hzT, hzO⟩
    · rintro ⟨hyT, hyO⟩
      exact ⟨⟨y, hyO⟩, hyT, rfl⟩
  rw [heq]
  exact hT.inter hO

/-- A continuous injective map from a nonempty open subset of `E` into `F`
    implies `Module.finrank ℝ E ≤ Module.finrank ℝ F`. -/
theorem finrank_le_of_continuous_injective_on_open {U : Set E}
    (hU : IsOpen U) (hneU : U.Nonempty) (f : U → F)
    (hf : Continuous f) (hinj : Function.Injective f) :
    Module.finrank ℝ E ≤ Module.finrank ℝ F := by
  obtain ⟨u, hu, hiu⟩ := exists_continuous_injective_into_open hU hneU
  exact dim_le_of_injective_continuous (fun x => f (u x)) (hf.comp hu) (hinj.comp hiu)

/-- If an open set `W₀ ⊆ X` is homeomorphic to an open set `O ⊆ F` and contains
    a nonempty open set `V ⊆ W₀` homeomorphic to an open set `U ⊆ E`, then
    `Module.finrank ℝ E = Module.finrank ℝ F`. -/
theorem finrank_eq_of_open_patch_in_chart {X : Type*} [TopologicalSpace X]
    {W₀ V : Set X} (hV : IsOpen V) (hVW₀ : V ⊆ W₀)
    {U : Set E} (hU : IsOpen U) (hneU : U.Nonempty)
    {O : Set F} (hO : IsOpen O) (φ : U ≃ₜ V) (e₀ : W₀ ≃ₜ O) :
    Module.finrank ℝ E = Module.finrank ℝ F := by
  let inc : V → W₀ := fun v => ⟨v.1, hVW₀ v.2⟩
  have hinc_cont : Continuous inc := continuous_subtype_val.subtype_mk _
  have hinc_inj : Function.Injective inc := fun a b h =>
    Subtype.ext (congrArg (fun w : W₀ => (w : X)) h)
  have hEF : Module.finrank ℝ E ≤ Module.finrank ℝ F :=
    finrank_le_of_continuous_injective_on_open hU hneU
      (fun u => (e₀ (inc (φ u)) : F))
      (continuous_subtype_val.comp (e₀.continuous.comp (hinc_cont.comp φ.continuous)))
      (Subtype.val_injective.comp (e₀.injective.comp (hinc_inj.comp φ.injective)))
  let S : Set O := {y : O | (e₀.symm y : X) ∈ V}
  have hS : IsOpen S := hV.preimage (continuous_subtype_val.comp e₀.symm.continuous)
  obtain ⟨T, hT, hTS⟩ := isOpen_induced_iff.mp hS
  let O' : Set F := T ∩ O
  have hO' : IsOpen O' := hT.inter hO
  have hmemS : ∀ y : O', (e₀.symm ⟨y.1, y.2.2⟩ : X) ∈ V := by
    intro y
    have hyT : (⟨y.1, y.2.2⟩ : O) ∈ Subtype.val ⁻¹' T := y.2.1
    rw [hTS] at hyT
    exact hyT
  have hneO' : O'.Nonempty := by
    obtain ⟨u₀, hu₀⟩ := hneU
    let y₀ : O := e₀ (inc (φ ⟨u₀, hu₀⟩))
    have hy₀S : y₀ ∈ S := by
      change (e₀.symm (e₀ (inc (φ ⟨u₀, hu₀⟩))) : X) ∈ V
      rw [e₀.symm_apply_apply]
      exact (φ ⟨u₀, hu₀⟩).2
    rw [← hTS] at hy₀S
    exact ⟨y₀.1, hy₀S, y₀.2⟩
  let toV : O' → V := fun y => ⟨(e₀.symm ⟨y.1, y.2.2⟩ : X), hmemS y⟩
  have htoV_cont : Continuous toV :=
    (continuous_subtype_val.comp
      (e₀.symm.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _
  have htoV_inj : Function.Injective toV := by
    intro a b hab
    have h1 : (e₀.symm ⟨a.1, a.2.2⟩ : W₀) = e₀.symm ⟨b.1, b.2.2⟩ :=
      Subtype.ext (congrArg (fun v : V => (v : X)) hab)
    have h2 : (⟨a.1, a.2.2⟩ : O) = ⟨b.1, b.2.2⟩ := e₀.symm.injective h1
    exact Subtype.ext (congrArg (fun y : O => (y : F)) h2)
  have hFE : Module.finrank ℝ F ≤ Module.finrank ℝ E :=
    finrank_le_of_continuous_injective_on_open hO' hneO'
      (fun y => (φ.symm (toV y) : E))
      (continuous_subtype_val.comp (φ.symm.continuous.comp htoV_cont))
      (Subtype.val_injective.comp (φ.symm.injective.comp htoV_inj))
  exact Nat.le_antisymm hEF hFE

/-- If every open neighborhood of `x ∈ X` contains a nonempty open patch homeomorphic to
    an open subset of `E`, then any open chart around `x` homeomorphic to an open subset
    of `F` forces `Module.finrank ℝ E = Module.finrank ℝ F`. -/
theorem finrank_eq_of_open_patch_near {X : Type*} [TopologicalSpace X] {x : X}
    (hpatch : ∀ W : Set X, IsOpen W → x ∈ W →
      ∃ (U : Set E) (V : Set X), IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V ⊆ W ∧ Nonempty (U ≃ₜ V))
    {W₀ : Set X} {O : Set F} (hW₀ : IsOpen W₀) (hxW₀ : x ∈ W₀) (hO : IsOpen O)
    (e₀ : W₀ ≃ₜ O) : Module.finrank ℝ E = Module.finrank ℝ F := by
  obtain ⟨U, V, hU, hV, hneU, hVW₀, ⟨φ⟩⟩ := hpatch W₀ hW₀ hxW₀
  exact finrank_eq_of_open_patch_in_chart hV hVW₀ hU hneU hO φ e₀

/-- Dimension-exclusion wrapper: if every open neighborhood of `x ∈ X` contains a
    nonempty open patch modeled on `E`, and `Module.finrank ℝ E ≠ Module.finrank ℝ F`
    (e.g. `10 ≠ 24`), then no open neighborhood of `x` is homeomorphic to an open
    subset of `F`. -/
theorem not_nhd_homeomorph_of_finrank_ne {X : Type*} [TopologicalSpace X] {x : X}
    (hpatch : ∀ W : Set X, IsOpen W → x ∈ W →
      ∃ (U : Set E) (V : Set X), IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V ⊆ W ∧ Nonempty (U ≃ₜ V))
    (hne : Module.finrank ℝ E ≠ Module.finrank ℝ F)
    {W₀ : Set X} {O : Set F} (hW₀ : IsOpen W₀) (hxW₀ : x ∈ W₀) (hO : IsOpen O) :
    IsEmpty (W₀ ≃ₜ O) :=
  ⟨fun e₀ => hne (finrank_eq_of_open_patch_near hpatch hW₀ hxW₀ hO e₀)⟩

/-- Single-sheet invariance-of-domain theorem (requiring NO openness hypothesis on `O ⊆ F`):
    Given a chart `e₀ : W₀ ≃ₜ O` around `x ∈ W₀` into an arbitrary subset `O ⊆ F`
    with `Module.finrank ℝ E = Module.finrank ℝ F`, and a continuous injective sheet
    `f₁ : U₁ → X` from an open set `U₁ ⊆ E` through `x`, the chart image `e₀ ⟨x, hxW₀⟩`
    lies in `interior O` (ruling out boundary points of manifolds with boundary) and
    `Set.range f₁` contains an open neighborhood of `x` in `X`. -/
theorem sheet_open_nhd_and_interior_of_chart {X : Type*} [TopologicalSpace X] {x : X}
    {W₀ : Set X} (hW₀ : IsOpen W₀) (hxW₀ : x ∈ W₀)
    {O : Set F} (e₀ : W₀ ≃ₜ O) (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {U₁ : Set E} (hU₁ : IsOpen U₁) {u₁ : E} (hu₁ : u₁ ∈ U₁)
    {f₁ : U₁ → X} (hf₁ : Continuous f₁) (hinj₁ : Function.Injective f₁)
    (hx₁ : f₁ ⟨u₁, hu₁⟩ = x) :
    (e₀ ⟨x, hxW₀⟩ : F) ∈ interior O ∧
      ∃ W₁ : Set X, IsOpen W₁ ∧ x ∈ W₁ ∧ W₁ ⊆ W₀ ∧ W₁ ⊆ Set.range f₁ := by
  let L : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hdim.symm
  let S₁ : Set U₁ := f₁ ⁻¹' W₀
  have hS₁ : IsOpen S₁ := hW₀.preimage hf₁
  let U₁' : Set E := (Subtype.val : U₁ → E) '' S₁
  have hU₁' : IsOpen U₁' := isOpen_subtype_val_image hU₁ hS₁
  have hzU₁ : ∀ z : U₁', z.1 ∈ U₁ := by
    rintro ⟨_, ⟨w, _, rfl⟩⟩
    exact w.2
  have hzW₀ : ∀ z : U₁', f₁ ⟨z.1, hzU₁ z⟩ ∈ W₀ := by
    rintro ⟨_, ⟨⟨w, hw⟩, hwS, rfl⟩⟩
    exact hwS
  let toW₀ : U₁' → W₀ := fun z => ⟨f₁ ⟨z.1, hzU₁ z⟩, hzW₀ z⟩
  have htoW₀_cont : Continuous toW₀ :=
    (hf₁.comp (continuous_subtype_val.subtype_mk hzU₁)).subtype_mk hzW₀
  have htoW₀_inj : Function.Injective toW₀ := by
    intro a b hab
    have h1 : f₁ ⟨a.1, hzU₁ a⟩ = f₁ ⟨b.1, hzU₁ b⟩ := congrArg Subtype.val hab
    have h2 : (⟨a.1, hzU₁ a⟩ : U₁) = ⟨b.1, hzU₁ b⟩ := hinj₁ h1
    exact Subtype.ext (congrArg (fun z : U₁ => (z : E)) h2)
  let g₁ : U₁' → E := fun z => L (e₀ (toW₀ z) : F)
  have hg₁_cont : Continuous g₁ :=
    L.continuous.comp (continuous_subtype_val.comp (e₀.continuous.comp htoW₀_cont))
  have hg₁_inj : Function.Injective g₁ :=
    L.injective.comp (Subtype.val_injective.comp (e₀.injective.comp htoW₀_inj))
  have hOpenRange : IsOpen (Set.range g₁) :=
    isOpen_range_of_continuous_injective hU₁' g₁ hg₁_cont hg₁_inj
  have hu₁' : u₁ ∈ U₁' := ⟨⟨u₁, hu₁⟩, by change f₁ ⟨u₁, hu₁⟩ ∈ W₀; rw [hx₁]; exact hxW₀, rfl⟩
  let z₀ : U₁' := ⟨u₁, hu₁'⟩
  have htoW₀_z₀ : toW₀ z₀ = ⟨x, hxW₀⟩ := Subtype.ext hx₁
  constructor
  · rw [mem_interior]
    refine ⟨L ⁻¹' Set.range g₁, ?_, hOpenRange.preimage L.continuous, ?_⟩
    · rintro y ⟨z, hz⟩
      have hLy : (e₀ (toW₀ z) : F) = y := L.injective hz
      rw [← hLy]
      exact (e₀ (toW₀ z)).2
    · exact ⟨z₀, by simp [g₁, htoW₀_z₀]⟩
  · let k : W₀ → E := fun w => L (e₀ w : F)
    have hk_cont : Continuous k :=
      L.continuous.comp (continuous_subtype_val.comp e₀.continuous)
    let S₀ : Set W₀ := k ⁻¹' Set.range g₁
    have hS₀ : IsOpen S₀ := hOpenRange.preimage hk_cont
    let W₁ : Set X := (Subtype.val : W₀ → X) '' S₀
    refine ⟨W₁, isOpen_subtype_val_image hW₀ hS₀, ?_, ?_, ?_⟩
    · refine ⟨⟨x, hxW₀⟩, ⟨z₀, ?_⟩, rfl⟩
      simp [k, g₁, htoW₀_z₀]
    · rintro _ ⟨w, _, rfl⟩
      exact w.2
    · rintro _ ⟨w, ⟨z, hz⟩, rfl⟩
      have h1 : (e₀ (toW₀ z) : F) = (e₀ w : F) := L.injective hz
      have h2 : toW₀ z = w := e₀.injective (Subtype.ext h1)
      exact ⟨⟨z.1, hzU₁ z⟩, congrArg Subtype.val h2⟩

/-- Two-sheet non-chart theorem for any subset `O ⊆ F` (including manifolds with boundary)
    when `Module.finrank ℝ E = Module.finrank ℝ F`: two continuous injective `E`-sheets
    through `x` with distinct image germs at `x` rule out any homeomorphism `W₀ ≃ₜ O`. -/
theorem not_nhd_homeomorph_of_two_sheets_of_finrank_eq {X : Type*} [TopologicalSpace X] {x : X}
    {U₁ U₂ : Set E} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    {u₁ u₂ : E} (hu₁ : u₁ ∈ U₁) (hu₂ : u₂ ∈ U₂)
    {f₁ : U₁ → X} {f₂ : U₂ → X}
    (hf₁ : Continuous f₁) (hinj₁ : Function.Injective f₁) (hx₁ : f₁ ⟨u₁, hu₁⟩ = x)
    (hf₂ : Continuous f₂) (hinj₂ : Function.Injective f₂) (hx₂ : f₂ ⟨u₂, hu₂⟩ = x)
    (hdistinct : ∀ W : Set X, IsOpen W → x ∈ W → W ∩ Set.range f₁ ≠ W ∩ Set.range f₂)
    {W₀ : Set X} {O : Set F} (hW₀ : IsOpen W₀) (hxW₀ : x ∈ W₀)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsEmpty (W₀ ≃ₜ O) := by
  refine ⟨fun e₀ => ?_⟩
  obtain ⟨_, W₁, hW₁, hxW₁, _, hsub₁⟩ :=
    sheet_open_nhd_and_interior_of_chart hW₀ hxW₀ e₀ hdim hU₁ hu₁ hf₁ hinj₁ hx₁
  obtain ⟨_, W₂, hW₂, hxW₂, _, hsub₂⟩ :=
    sheet_open_nhd_and_interior_of_chart hW₀ hxW₀ e₀ hdim hU₂ hu₂ hf₂ hinj₂ hx₂
  have hW : IsOpen (W₁ ∩ W₂) := hW₁.inter hW₂
  have hxW : x ∈ W₁ ∩ W₂ := ⟨hxW₁, hxW₂⟩
  have heq₁ : (W₁ ∩ W₂) ∩ Set.range f₁ = W₁ ∩ W₂ :=
    Set.inter_eq_left.mpr (Set.inter_subset_left.trans hsub₁)
  have heq₂ : (W₁ ∩ W₂) ∩ Set.range f₂ = W₁ ∩ W₂ :=
    Set.inter_eq_left.mpr (Set.inter_subset_right.trans hsub₂)
  exact hdistinct (W₁ ∩ W₂) hW hxW (heq₁.trans heq₂.symm)

/-- General two-sheet non-chart theorem:
    Suppose every open neighborhood of `x ∈ X` contains a nonempty open `E`-patch,
    and there are two continuous injective `E`-sheets `f₁ : U₁ → X` and `f₂ : U₂ → X`
    through `x` whose image germs at `x` are distinct. Then no open neighborhood `W₀`
    of `x` is homeomorphic to an open subset `O ⊆ F` for any finite-dimensional real
    inner-product space `F`. -/
theorem not_nhd_homeomorph_open_of_two_sheets {X : Type*} [TopologicalSpace X] {x : X}
    (hpatch : ∀ W : Set X, IsOpen W → x ∈ W →
      ∃ (U : Set E) (V : Set X), IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V ⊆ W ∧ Nonempty (U ≃ₜ V))
    {U₁ U₂ : Set E} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    {u₁ u₂ : E} (hu₁ : u₁ ∈ U₁) (hu₂ : u₂ ∈ U₂)
    {f₁ : U₁ → X} {f₂ : U₂ → X}
    (hf₁ : Continuous f₁) (hinj₁ : Function.Injective f₁) (hx₁ : f₁ ⟨u₁, hu₁⟩ = x)
    (hf₂ : Continuous f₂) (hinj₂ : Function.Injective f₂) (hx₂ : f₂ ⟨u₂, hu₂⟩ = x)
    (hdistinct : ∀ W : Set X, IsOpen W → x ∈ W → W ∩ Set.range f₁ ≠ W ∩ Set.range f₂)
    {W₀ : Set X} {O : Set F} (hW₀ : IsOpen W₀) (hxW₀ : x ∈ W₀) (hO : IsOpen O) :
    IsEmpty (W₀ ≃ₜ O) := by
  refine ⟨fun e₀ => ?_⟩
  have hdim : Module.finrank ℝ E = Module.finrank ℝ F :=
    finrank_eq_of_open_patch_near hpatch hW₀ hxW₀ hO e₀
  exact (not_nhd_homeomorph_of_two_sheets_of_finrank_eq
    hU₁ hU₂ hu₁ hu₂ hf₁ hinj₁ hx₁ hf₂ hinj₂ hx₂ hdistinct hW₀ hxW₀ hdim).false e₀

/-- Open-subtype invariance of domain for the existing sup-norm coordinate space. -/
theorem isOpen_range_of_continuous_injective_pi {n : ℕ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (f : U → (Fin n → ℝ)) (hf : Continuous f) (hinj : Function.Injective f) :
    IsOpen (Set.range f) := by
  let e : EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ) := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
  let g : (e ⁻¹' U) → EuclideanSpace ℝ (Fin n) := fun x => e.symm (f ⟨e x.1, x.2⟩)
  have hg : IsOpen (Set.range g) := isOpen_range_of_continuous_injective (hU.preimage e.continuous) g
    (e.symm.continuous.comp (hf.comp (e.continuous.comp continuous_subtype_val |>.subtype_mk _)))
    (fun x y hxy => Subtype.ext (e.injective (Subtype.ext_iff.mp (hinj (e.symm.injective hxy)))))
  have hr : e '' Set.range g = Set.range f := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨⟨e x.1, x.2⟩, by simp [g]⟩
    · rintro ⟨x, rfl⟩
      let x' : (e ⁻¹' U) := ⟨e.symm x.1, by simpa using x.2⟩
      exact ⟨g x', ⟨x', rfl⟩, by simp [g, x']⟩
  rw [← hr]
  exact e.isOpen_image.mpr hg

end TopologyReuse
