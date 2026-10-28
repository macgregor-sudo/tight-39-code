module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
public import GSAnalytic

@[expose] public section

/-!
# One simultaneous chart for finitely many families through a common germ (generic, Mathlib only)

Setting (MASTER §6.9). In a finite-dimensional real space `E`, analytic maps `m i : M → E`
(`i : ι`) and `fC : Pc → E` have injective strict derivatives at `0`; `fC` factors through each
`m i` near `0` by an analytic `ψ i` (the common germ lies in every family); and the derivative
images are as independent as their dimensions allow (`htrans`). Then one analytic chart
`Φ : Pc × (ι → U) × R → E`, with analytic inverse, straightens all of them at once: the family `i` is
the block `{u_j = 0 for j ≠ i, r = 0}` and the common germ is `{u = 0, r = 0}`.

Route: put `θ i (c, u) = ψ i c + L i u` with `L i` a linear complement of `range (dψ i)`, set
`F (c, u) = ∑ i m i (θ i (c, u i)) - (card ι - 1) • fC c`, and `Φ (c, u, r) = F (c, u) + K r` with `K` an
isomorphism of `R` onto a complement of `range dF`. One analytic inverse-function theorem
(`GSAnalytic.analyticAt_toOpenPartialHomeomorph_symm`) gives `Φ`; there is no separate embedding step.

`IsGermImage S x f p` says that the image under `f` of every small neighbourhood of `p` agrees with `S`
near `x`: `S` is the germ at `x` of the image of `f` near `p`.
-/

noncomputable section

open Filter Topology

namespace CKM.NativeFourFamily

/-- `S` is the germ at `x` of the image of `f` on small neighbourhoods of `p`. -/
def IsGermImage {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (S : Set X) (x : X) (f : P → X) (p : P) : Prop :=
  ∃ U₀ ∈ 𝓝 p, ∀ U ∈ 𝓝 p, U ⊆ U₀ → f '' U =ᶠ[𝓝 x] S

/-- Germ inclusion: images of small neighbourhoods of `p` under `f` lie in images of given
neighbourhoods of `q` under `g`. -/
def IsGermSubset {P Q X : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    (f : P → X) (p : P) (g : Q → X) (q : Q) : Prop :=
  ∀ V ∈ 𝓝 q, ∃ U ∈ 𝓝 p, f '' U ⊆ g '' V

/-- The common block `{u = 0, r = 0}`. -/
def commonBlock (ι Pc U R : Type*) [Zero U] [Zero R] : Set (Pc × (ι → U) × R) :=
  {z | z.2.1 = 0 ∧ z.2.2 = 0}

/-- The block of family `i`: `{u j = 0 for j ≠ i, r = 0}`. -/
def familyBlock {ι : Type*} (Pc U R : Type*) [Zero U] [Zero R] (i : ι) : Set (Pc × (ι → U) × R) :=
  {z | (∀ j, j ≠ i → z.2.1 j = 0) ∧ z.2.2 = 0}

/-- A linear map `L : U → W` whose range complements `range A`, given the dimension count. -/
private theorem chart_exists_complement {V W U : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    (A : V →L[ℝ] W)
    (h : Module.finrank ℝ (LinearMap.range (A : V →ₗ[ℝ] W)) + Module.finrank ℝ U =
      Module.finrank ℝ W) :
    ∃ L : U →L[ℝ] W, ∀ w, ∃ v u, A v + L u = w := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (LinearMap.range (A : V →ₗ[ℝ] W))
  have hd : Module.finrank ℝ U = Module.finrank ℝ Q := by
    have := Submodule.finrank_add_eq_of_isCompl hQ
    omega
  let e : U ≃ₗ[ℝ] Q := LinearEquiv.ofFinrankEq U Q hd
  refine ⟨(Q.subtype ∘ₗ e.toLinearMap).toContinuousLinearMap, fun w => ?_⟩
  have hw : w ∈ LinearMap.range (A : V →ₗ[ℝ] W) ⊔ Q := by
    rw [hQ.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, q, hq, hyq⟩ := Submodule.mem_sup.1 hw
  obtain ⟨v, rfl⟩ := hy
  refine ⟨v, e.symm ⟨q, hq⟩, ?_⟩
  simpa using hyq

/-- A surjective linear map between spaces of equal finite dimension, as a linear isomorphism. -/
private def chartCLE {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (T : X →L[ℝ] Y) (hT : Function.Surjective T)
    (hd : Module.finrank ℝ X = Module.finrank ℝ Y) : X ≃L[ℝ] Y :=
  (LinearEquiv.ofBijective (T : X →ₗ[ℝ] Y)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).2 hT, hT⟩).toContinuousLinearEquiv

/-- `chartCLE T` has underlying map `T`. -/
private theorem chartCLE_coe {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (T : X →L[ℝ] Y) (hT : Function.Surjective T)
    (hd : Module.finrank ℝ X = Module.finrank ℝ Y) :
    (chartCLE T hT hd : X →L[ℝ] Y) = T := by
  ext x; rfl

/-- Analytic inverse function theorem, restricted to an open set on which the map and its
inverse are analytic. The local inverse of a map with invertible strict derivative is the inverse
function theorem (J. Dieudonné, *Foundations of Modern Analysis*, 1960, (10.2.5)); its analyticity is
the analytic inverse function theorem (E. F. Whittlesey, *Analytic functions in Banach spaces*,
Proc. Amer. Math. Soc. 16 (1965), 1077–1083), here via GS's
`analyticAt_toOpenPartialHomeomorph_symm`; analyticity is an open condition (`isOpen_analyticAt`). -/
private theorem chart_exists_analytic_oph {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (f : X → Y) (e : X ≃L[ℝ] Y) (a : X) (hf : HasStrictFDerivAt f (e : X →L[ℝ] Y) a)
    (ha : AnalyticAt ℝ f a) :
    ∃ Φ : OpenPartialHomeomorph X Y, (⇑Φ = f) ∧ a ∈ Φ.source ∧
      AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target := by
  set Φ₀ := hf.toOpenPartialHomeomorph f with hΦ₀
  have hsymm : AnalyticAt ℝ Φ₀.symm (f a) :=
    CKM.NativeGroupSlice.analyticAt_toOpenPartialHomeomorph_symm hf ha
  have hcoe : ⇑Φ₀ = f := hf.toOpenPartialHomeomorph_coe
  have ha0 : a ∈ Φ₀.source := hf.mem_toOpenPartialHomeomorph_source
  let S : Set X := {x | AnalyticAt ℝ f x} ∩ (Φ₀.source ∩ Φ₀ ⁻¹' {y | AnalyticAt ℝ Φ₀.symm y})
  have hS : IsOpen S :=
    (isOpen_analyticAt ℝ f).inter (Φ₀.isOpen_inter_preimage (isOpen_analyticAt ℝ _))
  refine ⟨Φ₀.restrOpen S hS, by simp [hcoe], ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    refine ⟨ha0, ha, ha0, ?_⟩
    show AnalyticAt ℝ Φ₀.symm (Φ₀ a)
    rw [hcoe]; exact hsymm
  · intro x hx
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    rw [OpenPartialHomeomorph.coe_restrOpen, hcoe]
    exact hx.2.1
  · intro y hy
    have hy' : y ∈ Φ₀.target ∧ Φ₀.symm y ∈ S := hy
    rw [OpenPartialHomeomorph.coe_restrOpen_symm]
    have h := hy'.2.2.2
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at h
    rwa [Φ₀.right_inv hy'.1] at h


/-- A block parametrized by `j` (with retraction `π`) and a map `g ∘ h = Φ ∘ j` near the base,
`h` open at the base: the image of the block is the germ of the image of `g`. -/
private theorem chart_isGermImage_of_param {X Y Z P : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace P]
    (Φ : OpenPartialHomeomorph X Y) {a : X} (ha : a ∈ Φ.source) (B : Set X)
    (j : Z → X) (π : X → Z) (h : Z → P) (g : P → Y) {z₀ : Z} {p : P}
    (hj : ContinuousAt j z₀) (hja : j z₀ = a) (hjB : ∀ z, j z ∈ B)
    (hπ : ContinuousAt π a) (hπa : π a = z₀) (hπB : ∀ x ∈ B, j (π x) = x)
    (hh : ContinuousAt h z₀) (hhp : h z₀ = p) (hopen : ∀ W ∈ 𝓝 z₀, h '' W ∈ 𝓝 p)
    (hg : ∀ᶠ z in 𝓝 z₀, g (h z) = Φ (j z)) :
    IsGermImage (Φ '' (Φ.source ∩ B)) (Φ a) g p := by
  set W : Set Z := {z | j z ∈ Φ.source ∧ g (h z) = Φ (j z)} with hWdef
  have hW : W ∈ 𝓝 z₀ := by
    have h1 : ∀ᶠ z in 𝓝 z₀, j z ∈ Φ.source :=
      hj.preimage_mem_nhds (by rw [hja]; exact Φ.open_source.mem_nhds ha)
    exact h1.and hg
  refine ⟨h '' W, hopen W hW, fun U hU hUW => ?_⟩
  rw [Filter.eventuallyEqSet_iff]
  have hN : ∀ᶠ y in 𝓝 (Φ a), y ∈ Φ.target ∧ π (Φ.symm y) ∈ W ∩ h ⁻¹' U := by
    refine Filter.Eventually.and (Φ.open_target.mem_nhds (Φ.map_source ha)) ?_
    have hc : ContinuousAt (fun y => π (Φ.symm y)) (Φ a) := by
      refine ContinuousAt.comp (f := Φ.symm) (g := π) ?_ (Φ.continuousAt_symm (Φ.map_source ha))
      rw [Φ.left_inv ha]; exact hπ
    refine hc.preimage_mem_nhds ?_
    rw [Φ.left_inv ha, hπa]
    exact Filter.inter_mem hW (hh.preimage_mem_nhds (by rw [hhp]; exact hU))
  filter_upwards [hN] with y hy
  constructor
  · rintro ⟨x, hxU, rfl⟩
    obtain ⟨z, hzW, rfl⟩ := hUW hxU
    exact ⟨j z, ⟨hzW.1, hjB z⟩, hzW.2.symm⟩
  · rintro ⟨x, ⟨hxs, hxB⟩, rfl⟩
    have hx : Φ.symm (Φ x) = x := Φ.left_inv hxs
    have h2 := hy.2
    rw [hx] at h2
    refine ⟨h (π x), h2.2, ?_⟩
    rw [h2.1.2, hπB x hxB]

/-- Derivative identity from a factorization near the base point. -/
private theorem chart_comp_eq {Pc M E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Pc] [NormedSpace ℝ Pc]
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    {fC : Pc → E} {m : M → E} {ψ : Pc → M} {fC' : Pc →L[ℝ] E} {m' : M →L[ℝ] E}
    {ψ' : Pc →L[ℝ] M} (hfC' : HasStrictFDerivAt fC fC' 0) (hm' : HasStrictFDerivAt m m' 0)
    (hψ' : HasStrictFDerivAt ψ ψ' 0) (hψ0 : ψ 0 = 0)
    (hincl : ∀ᶠ c in 𝓝 (0 : Pc), m (ψ c) = fC c) : m'.comp ψ' = fC' := by
  have hm0 : HasFDerivAt m m' (ψ 0) := by rw [hψ0]; exact hm'.hasFDerivAt
  have h1 : HasFDerivAt (fun c => m (ψ c)) (m'.comp ψ') 0 := hm0.comp 0 hψ'.hasFDerivAt
  have h2 : HasFDerivAt (fun c => m (ψ c)) fC' 0 := hfC'.hasFDerivAt.congr_of_eventuallyEq hincl
  exact h1.unique h2

theorem exists_simultaneous_chart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E Pc M U R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Pc] [NormedSpace ℝ Pc] [FiniteDimensional ℝ Pc]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    (fC : Pc → E) (m : ι → M → E) (ψ : ι → Pc → M)
    (fC' : Pc →L[ℝ] E) (m' : ι → M →L[ℝ] E)
    (hfC : AnalyticAt ℝ fC 0) (hfC' : HasStrictFDerivAt fC fC' 0)
    (hfC'i : Function.Injective fC')
    (hm : ∀ i, AnalyticAt ℝ (m i) 0) (hm' : ∀ i, HasStrictFDerivAt (m i) (m' i) 0)
    (hm'i : ∀ i, Function.Injective (m' i))
    (hψ : ∀ i, AnalyticAt ℝ (ψ i) 0) (hψ0 : ∀ i, ψ i 0 = 0)
    (hincl : ∀ i, ∀ᶠ c in 𝓝 (0 : Pc), m i (ψ i c) = fC c)
    (hdimU : Module.finrank ℝ Pc + Module.finrank ℝ U = Module.finrank ℝ M)
    (hdimR : Module.finrank ℝ Pc + Fintype.card ι * Module.finrank ℝ U + Module.finrank ℝ R =
      Module.finrank ℝ E)
    (htrans : Module.finrank ℝ ↥(⨆ i, LinearMap.range ((m' i : M →L[ℝ] E) : M →ₗ[ℝ] E)) =
      Module.finrank ℝ Pc + Fintype.card ι * Module.finrank ℝ U) :
    ∃ Φ : OpenPartialHomeomorph (Pc × (ι → U) × R) E,
      (0 : Pc × (ι → U) × R) ∈ Φ.source ∧ Φ 0 = fC 0 ∧
      AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧
      IsGermImage (Φ '' (Φ.source ∩ commonBlock ι Pc U R)) (fC 0) fC 0 ∧
      (∀ i, IsGermImage (Φ '' (Φ.source ∩ familyBlock Pc U R i)) (fC 0) (m i) 0) ∧
      (∀ i j, i ≠ j →
        Φ '' (Φ.source ∩ familyBlock Pc U R i) ∩ Φ '' (Φ.source ∩ familyBlock Pc U R j) =
          Φ '' (Φ.source ∩ commonBlock ι Pc U R)) := by
  classical
  have : CompleteSpace (Pc × (ι → U) × R) := FiniteDimensional.complete ℝ _
  have : CompleteSpace (Pc × U) := FiniteDimensional.complete ℝ _
  have : CompleteSpace E := FiniteDimensional.complete ℝ _
  have : CompleteSpace M := FiniteDimensional.complete ℝ _
  -- Step 1: derivatives of `ψ i` and the factorization `m' i ∘ ψ' i = fC'`.
  let ψ' : ι → Pc →L[ℝ] M := fun i => fderiv ℝ (ψ i) 0
  have hψs : ∀ i, HasStrictFDerivAt (ψ i) (ψ' i) 0 := fun i => (hψ i).hasStrictFDerivAt
  have hcomp : ∀ i, (m' i).comp (ψ' i) = fC' := fun i =>
    chart_comp_eq hfC' (hm' i) (hψs i) (hψ0 i) (hincl i)
  have hcomp' : ∀ i c, m' i (ψ' i c) = fC' c := fun i c => by
    rw [← hcomp i]; rfl
  have hψinj : ∀ i, Function.Injective (ψ' i) := fun i a b hab =>
    hfC'i (by rw [← hcomp' i a, ← hcomp' i b, hab])
  -- Step 2: complements `L i` of `range (ψ' i)` and the maps `θ i`.
  have hLex : ∀ i, ∃ L : U →L[ℝ] M, ∀ w, ∃ v u, ψ' i v + L u = w := fun i =>
    chart_exists_complement (ψ' i) (by
      rw [LinearMap.finrank_range_of_inj (hψinj i)]; exact hdimU)
  choose L hL using hLex
  let θ : ι → Pc × U → M := fun i z => ψ i z.1 + L i z.2
  let T : ι → Pc × U →L[ℝ] M := fun i =>
    (ψ' i).comp (ContinuousLinearMap.fst ℝ Pc U) + (L i).comp (ContinuousLinearMap.snd ℝ Pc U)
  have hTs : ∀ i, Function.Surjective (T i) := fun i w => by
    obtain ⟨v, u, h⟩ := hL i w
    exact ⟨(v, u), by simpa [T] using h⟩
  have hTd : Module.finrank ℝ (Pc × U) = Module.finrank ℝ M := by
    rw [Module.finrank_prod]; exact hdimU
  let Te : ι → (Pc × U) ≃L[ℝ] M := fun i => chartCLE (T i) (hTs i) hTd
  have hTe : ∀ i w, Te i w = ψ' i w.1 + L i w.2 := fun i w => rfl
  have hθ0 : ∀ i, θ i 0 = 0 := fun i => by simp [θ, hψ0 i]
  have hθs : ∀ i, HasStrictFDerivAt (θ i) (Te i : Pc × U →L[ℝ] M) 0 := fun i => by
    rw [chartCLE_coe]
    exact ((hψs i).comp (0 : Pc × U) hasStrictFDerivAt_fst).add
      ((L i).hasStrictFDerivAt.comp (0 : Pc × U) hasStrictFDerivAt_snd)
  have hθa : ∀ i, AnalyticAt ℝ (θ i) 0 := fun i =>
    ((hψ i).comp_of_eq ((ContinuousLinearMap.fst ℝ Pc U).analyticAt 0) (map_zero _)).add
      (((L i).comp (ContinuousLinearMap.snd ℝ Pc U)).analyticAt 0)
  -- Step 3: the linear map `G` and its rank.
  let G : Pc × (ι → U) →L[ℝ] E := fC'.comp (ContinuousLinearMap.fst ℝ Pc (ι → U)) +
    ∑ i, (m' i).comp ((L i).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => U) i).comp
      (ContinuousLinearMap.snd ℝ Pc (ι → U))))
  have hG : ∀ c u, G (c, u) = fC' c + ∑ i, m' i (L i (u i)) := fun c u => by
    simp [G]
  have hGr : ∀ i, LinearMap.range ((m' i : M →L[ℝ] E) : M →ₗ[ℝ] E) ≤
      LinearMap.range ((G : Pc × (ι → U) →L[ℝ] E) : Pc × (ι → U) →ₗ[ℝ] E) := by
    intro i y hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨c, u, rfl⟩ := hL i x
    refine ⟨(c, Pi.single i u), ?_⟩
    show G (c, Pi.single i u) = m' i (ψ' i c + L i u)
    rw [hG, map_add, hcomp' i c, Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hdimX : Module.finrank ℝ (Pc × (ι → U)) =
      Module.finrank ℝ Pc + Fintype.card ι * Module.finrank ℝ U := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype]; simp
  have hGrank : Module.finrank ℝ
      (LinearMap.range ((G : Pc × (ι → U) →L[ℝ] E) : Pc × (ι → U) →ₗ[ℝ] E)) =
      Module.finrank ℝ Pc + Fintype.card ι * Module.finrank ℝ U := by
    apply le_antisymm
    · rw [← hdimX]; exact LinearMap.finrank_range_le _
    · rw [← htrans]; exact Submodule.finrank_mono (iSup_le hGr)
  obtain ⟨K, hK⟩ := chart_exists_complement (U := R) G (by rw [hGrank]; exact hdimR)
  -- Step 4: the chart map and its derivative.
  let Φf : Pc × (ι → U) × R → E := fun z =>
    fC z.1 + ∑ i, (m i (θ i (z.1, z.2.1 i)) - fC z.1) + K z.2.2
  let D : Pc × (ι → U) × R →L[ℝ] E :=
    G.comp ((ContinuousLinearMap.fst ℝ Pc ((ι → U) × R)).prod
      ((ContinuousLinearMap.fst ℝ (ι → U) R).comp (ContinuousLinearMap.snd ℝ Pc ((ι → U) × R)))) +
    K.comp ((ContinuousLinearMap.snd ℝ (ι → U) R).comp (ContinuousLinearMap.snd ℝ Pc ((ι → U) × R)))
  have hD : ∀ z, D z = G (z.1, z.2.1) + K z.2.2 := fun z => rfl
  have hDs : Function.Surjective D := fun w => by
    obtain ⟨v, r, h⟩ := hK w
    exact ⟨(v.1, v.2, r), by rw [hD]; exact h⟩
  have hDd : Module.finrank ℝ (Pc × (ι → U) × R) = Module.finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_pi_fintype, ← hdimR]
    simp [add_assoc]
  let P : ι → Pc × (ι → U) × R →L[ℝ] Pc × U := fun i =>
    (ContinuousLinearMap.fst ℝ Pc ((ι → U) × R)).prod
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => U) i).comp
        ((ContinuousLinearMap.fst ℝ (ι → U) R).comp (ContinuousLinearMap.snd ℝ Pc ((ι → U) × R))))
  have hP : ∀ i z, P i z = (z.1, z.2.1 i) := fun i z => rfl
  have hΦd : HasStrictFDerivAt Φf D 0 := by
    have hsum : ∀ i ∈ (Finset.univ : Finset ι), HasStrictFDerivAt
        (fun z : Pc × (ι → U) × R => m i (θ i (P i z)) - fC z.1)
        ((m' i).comp ((Te i : Pc × U →L[ℝ] M).comp (P i)) -
          fC'.comp (ContinuousLinearMap.fst ℝ Pc ((ι → U) × R))) 0 := by
      intro i _
      have h1 : HasStrictFDerivAt (θ i) (Te i : Pc × U →L[ℝ] M) (P i 0) := by
        rw [map_zero]; exact hθs i
      have h2 : HasStrictFDerivAt (m i) (m' i) (θ i (P i 0)) := by
        rw [map_zero, hθ0]; exact hm' i
      exact (HasStrictFDerivAt.comp (f := fun z => θ i (P i z)) 0 h2
        (h1.comp 0 (P i).hasStrictFDerivAt)).fun_sub
        (hfC'.comp (0 : Pc × (ι → U) × R) hasStrictFDerivAt_fst)
    have h := ((hfC'.comp (0 : Pc × (ι → U) × R) hasStrictFDerivAt_fst).fun_add
      (HasStrictFDerivAt.fun_sum hsum)).fun_add
      (K.comp ((ContinuousLinearMap.snd ℝ (ι → U) R).comp
        (ContinuousLinearMap.snd ℝ Pc ((ι → U) × R)))).hasStrictFDerivAt
    refine h.congr_fderiv (ContinuousLinearMap.ext fun z => ?_)
    rw [hD, hG]
    simp only [add_apply, sum_apply, sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, hTe, hP,
      map_add, hcomp', ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      add_sub_cancel_left]
  have hΦa : AnalyticAt ℝ Φf 0 := by
    have hfst : AnalyticAt ℝ (fun z : Pc × (ι → U) × R => fC z.1) 0 :=
      hfC.comp_of_eq ((ContinuousLinearMap.fst ℝ Pc ((ι → U) × R)).analyticAt 0) rfl
    have hsum : ∀ i ∈ (Finset.univ : Finset ι), AnalyticAt ℝ
        (fun z : Pc × (ι → U) × R => m i (θ i (P i z)) - fC z.1) 0 := by
      intro i _
      have h1 : AnalyticAt ℝ (fun z => θ i (P i z)) 0 :=
        (hθa i).comp_of_eq ((P i).analyticAt 0) (map_zero _)
      have h2 : AnalyticAt ℝ (fun z => m i (θ i (P i z))) 0 :=
        (hm i).comp_of_eq h1 (by rw [map_zero, hθ0])
      exact h2.sub hfst
    exact (hfst.add
      (Finset.analyticAt_fun_sum _ hsum)).add
      ((K.comp ((ContinuousLinearMap.snd ℝ (ι → U) R).comp
        (ContinuousLinearMap.snd ℝ Pc ((ι → U) × R)))).analyticAt 0)
  -- Step 5: the analytic chart and its blocks.
  obtain ⟨Φ, hΦf, h0s, hΦan, hΦsan⟩ := chart_exists_analytic_oph Φf (chartCLE D hDs hDd) 0
    (by rw [chartCLE_coe]; exact hΦd) hΦa
  have hm0 : ∀ i, m i 0 = fC 0 := fun i => by
    rw [← hψ0 i]; exact (hincl i).self_of_nhds
  have hΦ0 : Φ 0 = fC 0 := by
    rw [hΦf]
    show fC 0 + ∑ i, (m i (θ i (0, 0)) - fC 0) + K 0 = fC 0
    have h : ∀ i, θ i (0, 0) = 0 := hθ0
    simp [h, hm0]
  refine ⟨Φ, h0s, hΦ0, hΦan, hΦsan, ?_, ?_, ?_⟩
  · rw [← hΦ0]
    refine chart_isGermImage_of_param Φ h0s _ (fun c : Pc => ((c, 0, 0) : Pc × (ι → U) × R))
      Prod.fst id fC ((continuous_id.prodMk continuous_const).continuousAt) rfl
      (fun c => ⟨rfl, rfl⟩) continuousAt_fst rfl ?_ continuousAt_id rfl
      (fun W hW => by rwa [Set.image_id]) ?_
    · rintro x ⟨h1, h2⟩; exact Prod.ext rfl (Prod.ext h1.symm h2.symm)
    · filter_upwards [Filter.eventually_all.2 hincl] with c hc
      rw [hΦf]
      show fC c = fC c + ∑ i, (m i (θ i (c, 0)) - fC c) + K 0
      simp [θ, hc]
  · intro i
    rw [← hΦ0]
    have hθo : ∀ W ∈ 𝓝 (0 : Pc × U), θ i '' W ∈ 𝓝 (0 : M) := fun W hW => by
      have h := (hθs i).map_nhds_eq_of_equiv
      rw [hθ0] at h
      rw [← h]; exact Filter.image_mem_map hW
    refine chart_isGermImage_of_param Φ h0s _
      (fun w : Pc × U => ((w.1, Pi.single i w.2, 0) : Pc × (ι → U) × R))
      (fun z => (z.1, z.2.1 i)) (θ i) (m i) ?_ ?_ ?_ ?_ rfl ?_ (hθs i).continuousAt (hθ0 i) hθo ?_
    · exact (continuous_fst.prodMk
        (((ContinuousLinearMap.single ℝ (fun _ : ι => U) i).continuous.comp continuous_snd).prodMk
          continuous_const)).continuousAt
    · ext <;> simp
    · intro w; exact ⟨fun k hk => by simp [hk], rfl⟩
    · fun_prop
    · rintro x ⟨h1, h2⟩
      refine Prod.ext rfl (Prod.ext (funext fun k => ?_) h2.symm)
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk, h1 k hk]
    · filter_upwards [continuousAt_fst.tendsto.eventually (Filter.eventually_all.2 hincl)]
        with w hw
      rw [hΦf]
      show m i (θ i w) = fC w.1 + ∑ k, (m k (θ k (w.1, (Pi.single i w.2 : ι → U) k)) - fC w.1) + K 0
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [θ, hk, hw k]
      · intro h; exact absurd (Finset.mem_univ i) h
  · intro i j hij
    rw [← Φ.injOn.image_inter Set.inter_subset_left Set.inter_subset_left]
    congr 1
    ext z
    simp only [Set.mem_inter_iff, familyBlock, commonBlock, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hs, hi, hr⟩, _, hj, _⟩
      refine ⟨hs, funext fun k => ?_, hr⟩
      by_cases hk : k = i
      · subst hk; exact hj k hij
      · exact hi k hk
    · rintro ⟨hs, hu, hr⟩
      exact ⟨⟨hs, fun k _ => by rw [hu]; rfl, hr⟩, hs, fun k _ => by rw [hu]; rfl, hr⟩

/-- Germ images that agree as germs intersect as germs. -/
theorem IsGermImage.inter_eventuallyEq {P Q X : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    [TopologicalSpace X] {S T : Set X} {x : X} {f : P → X} {p : P} {g : Q → X} {q : Q}
    (hf : IsGermImage S x f p) (hg : IsGermImage T x g q) :
    ∃ U₀ ∈ 𝓝 p, ∃ V₀ ∈ 𝓝 q, ∀ U ∈ 𝓝 p, U ⊆ U₀ → ∀ V ∈ 𝓝 q, V ⊆ V₀ →
      (f '' U ∩ g '' V) =ᶠ[𝓝 x] (S ∩ T) := by
  obtain ⟨U₀, hU₀, hfU⟩ := hf
  obtain ⟨V₀, hV₀, hgV⟩ := hg
  exact ⟨U₀, hU₀, V₀, hV₀, fun U hU hUU V hV hVV => (hfU U hU hUU).inter (hgV V hV hVV)⟩

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.exists_simultaneous_chart
#print axioms CKM.NativeFourFamily.IsGermImage.inter_eventuallyEq
