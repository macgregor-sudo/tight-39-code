module

public import TopologyPreflight.ConditionalIoD
public import FixedPointTheorems.brouwer

@[expose] public section

/-!
Adapter from the general Brouwer theorem to the finite-dimensional ball.
The proof uses the upstream general Brouwer theorem on the closed unit ball.
-/

namespace TopologyReuse

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

instance instBrouwerFixedPoint : BrouwerFixedPoint E where
  brouwer_fixed_point f hf :=
    _root_.brouwer_fixed_point
      (Metric.closedBall (0 : E) 1)
      (convex_closedBall (0 : E) 1)
      (isCompact_closedBall (0 : E) 1)
      ⟨0, by simp⟩
      ⟨f, hf⟩

/-- Unconditional invariance of domain, requiring continuity only on the domain. -/
theorem isOpen_image_of_continuousOn_injOn (f : E → E) (U : Set E)
    (hU : IsOpen U) (hf : ContinuousOn f U) (hinj : Set.InjOn f U) :
    IsOpen (f '' U) :=
  invariance_of_domain_open_map f U hU hf hinj

/-- A continuous injective map defined only on an open subtype has open image. -/
theorem isOpen_range_of_continuous_injective {U : Set E} (hU : IsOpen U)
    (f : U → E) (hf : Continuous f) (hinj : Function.Injective f) :
    IsOpen (Set.range f) := by
  classical
  let g : E → E := fun x => if hx : x ∈ U then f ⟨x, hx⟩ else 0
  have hrestrict : (fun x : U => g x) = f := by
    funext x
    simp [g, x.property]
  have hg : ContinuousOn g U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun x : U => g x)
    rw [hrestrict]
    exact hf
  have hginj : Set.InjOn g U := by
    intro x hx y hy hxy
    have hsub : (⟨x, hx⟩ : U) = ⟨y, hy⟩ :=
      hinj (by simpa [g, hx, hy] using hxy)
    exact congrArg Subtype.val hsub
  have himage : g '' U = Set.range f := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, by simp [g, hx]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, by simp [g, x.property]⟩
  rw [← himage]
  exact isOpen_image_of_continuousOn_injOn g U hU hg hginj

end TopologyReuse
