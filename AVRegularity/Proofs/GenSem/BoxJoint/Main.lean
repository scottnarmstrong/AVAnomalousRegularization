-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Construction.DiagLetter
public import Mathlib.Analysis.Calculus.FDeriv.Partial

section
@[expose] public section
open Filter Topology Set
namespace AVRegularity.Providers.GenSem

/-! Interchange of the slow and fast derivatives.

If the fast derivative `H X z` of `G X` is differentiable in the slow variable `X`, and the
slow derivative of `H` is jointly continuous, then the slow derivative of `G` is differentiable in
the fast variable, with derivative the slow derivative of `H` with the arguments flipped. -/

variable {D Z E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dist_le_two_mul_of_dist_lt {G : Type*} [PseudoMetricSpace G] {a b c : G} {r : ℝ}
    (h1 : dist a c < r) (h2 : dist b c < r) : dist a b ≤ 2 * r := by
  have := dist_triangle_right a b c
  linarith

/-- Mean value estimate for a difference quotient of a map `K`, in a ball around `X₀`. -/
theorem dist_slope_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : D → F}
    {X₀ : D} {ρ C : ℝ} (hρ : 0 < ρ)
    (hK : ∀ X ∈ Metric.ball X₀ ρ, DifferentiableAt ℝ K X)
    (hb : ∀ X ∈ Metric.ball X₀ ρ, dist (fderiv ℝ K X) (fderiv ℝ K X₀) ≤ C)
    {h : ℝ} (hh0 : h ≠ 0) {w : D} (hhw : ‖h • w‖ < ρ) :
    dist (fderiv ℝ K X₀ w) (h⁻¹ • (K (X₀ + h • w) - K X₀)) ≤ C * ‖w‖ := by
  set L : D →L[ℝ] F := fderiv ℝ K X₀ with hL
  set ψ : D → F := fun X => K X - L (X - X₀) with hψ
  have hbound : ∀ X ∈ Metric.ball X₀ ρ, ‖fderiv ℝ K X - L‖ ≤ C := by
    intro X hX
    rw [← dist_eq_norm]
    exact hb X hX
  have hder : ∀ X ∈ Metric.ball X₀ ρ,
      HasFDerivWithinAt ψ (fderiv ℝ K X - L) (Metric.ball X₀ ρ) X := by
    intro X hX
    have hl : HasFDerivAt (fun X => L (X - X₀)) L X := by
      have h2 := (L.hasFDerivAt (x := X - X₀)).comp X ((hasFDerivAt_id X).sub_const X₀)
      rw [ContinuousLinearMap.comp_id] at h2
      exact h2
    exact ((hK X hX).hasFDerivAt.sub hl).hasFDerivWithinAt
  have hmvt := (convex_ball X₀ ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound
    (Metric.mem_ball_self hρ) (y := X₀ + h • w) (by simpa using hhw)
  have hψdiff : ψ (X₀ + h • w) - ψ X₀ = K (X₀ + h • w) - K X₀ - h • L w := by
    simp [hψ]
    abel
  have hkey : L w - h⁻¹ • (K (X₀ + h • w) - K X₀) = -(h⁻¹ • (ψ (X₀ + h • w) - ψ X₀)) := by
    rw [hψdiff]
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hh0, one_smul]
    abel
  rw [dist_eq_norm, hkey, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs]
  have hn : ‖ψ (X₀ + h • w) - ψ X₀‖ ≤ C * (|h| * ‖w‖) := by
    have := hmvt
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at this
    exact this
  have habs : 0 < |h| := abs_pos.mpr hh0
  calc |h|⁻¹ * ‖ψ (X₀ + h • w) - ψ X₀‖ ≤ |h|⁻¹ * (C * (|h| * ‖w‖)) := by gcongr
    _ = C * ‖w‖ := by field_simp

/-- Directional version of the interchange: the `w`-slow derivative of `G` is fast-differentiable. -/
theorem hasFDerivAt_slowDirDeriv_of_mixed {Ω : Set D} (hΩ : IsOpen Ω)
    {G : D → Z → E} {H : D → Z → (Z →L[ℝ] E)}
    (h1 : ∀ X ∈ Ω, ∀ z, HasFDerivAt (G X) (H X z) z)
    (h2 : ∀ z, DifferentiableOn ℝ (fun X => G X z) Ω)
    (h3 : ∀ z, DifferentiableOn ℝ (fun X => H X z) Ω)
    (h4 : ContinuousOn (fun p : D × Z => fderiv ℝ (fun X => H X p.2) p.1) (Ω ×ˢ Set.univ))
    {X₀ : D} (hX₀ : X₀ ∈ Ω) (w : D) (z₀ : Z) :
    HasFDerivAt (fun z => fderiv ℝ (fun X => G X z) X₀ w)
      (fderiv ℝ (fun X => H X z₀) X₀ w) z₀ := by
  have hev : ∀ᶠ h : ℝ in 𝓝[≠] 0, X₀ + h • w ∈ Ω := by
    have hc : Continuous (fun h : ℝ => X₀ + h • w) := by fun_prop
    have ht : Tendsto (fun h : ℝ => X₀ + h • w) (𝓝 0) (𝓝 X₀) := by
      simpa using hc.tendsto 0
    exact (ht.eventually (hΩ.mem_nhds hX₀)).filter_mono nhdsWithin_le_nhds
  refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := 𝓝[≠] (0 : ℝ))
    (f := fun h z => h⁻¹ • (G (X₀ + h • w) z - G X₀ z))
    (f' := fun h z => h⁻¹ • (H (X₀ + h • w) z - H X₀ z))
    (g' := fun z => fderiv ℝ (fun X => H X z) X₀ w) ?_ ?_ ?_
  · -- uniform convergence of the fast derivatives
    rw [Metric.tendstoUniformlyOnFilter_iff]
    intro ε hε
    set c : ℝ := ‖w‖ + 1 with hc
    have hcpos : 0 < c := by positivity
    have hε₁ : 0 < ε / (4 * c) := by positivity
    have hcont : ContinuousAt (fun p : D × Z => fderiv ℝ (fun X => H X p.2) p.1) (X₀, z₀) :=
      h4.continuousAt ((hΩ.prod isOpen_univ).mem_nhds ⟨hX₀, mem_univ _⟩)
    have hmem := hcont.preimage_mem_nhds
      (Metric.ball_mem_nhds (fderiv ℝ (fun X => H X z₀) X₀) hε₁)
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hmem
    have hδc : ∀ p : D × Z, dist p (X₀, z₀) < δ →
        dist (fderiv ℝ (fun X => H X p.2) p.1) (fderiv ℝ (fun X => H X z₀) X₀) <
          ε / (4 * c) := fun p hp => Metric.mem_ball.mp (hsub (Metric.mem_ball.mpr hp))
    obtain ⟨ρΩ, hρΩ, hball⟩ := Metric.isOpen_iff.mp hΩ X₀ hX₀
    set ρ : ℝ := min δ ρΩ with hρ
    have hρpos : 0 < ρ := lt_min hδ hρΩ
    have hbΩ : Metric.ball X₀ ρ ⊆ Ω := fun x hx =>
      hball (Metric.ball_subset_ball (min_le_right _ _) hx)
    have hh : ∀ᶠ h : ℝ in 𝓝[≠] 0, h ≠ 0 ∧ ‖h • w‖ < ρ := by
      have h1' : ∀ᶠ h : ℝ in 𝓝[≠] 0, h ≠ 0 := self_mem_nhdsWithin
      have hc2 : Continuous (fun h : ℝ => ‖h • w‖) := by fun_prop
      have ht : Tendsto (fun h : ℝ => ‖h • w‖) (𝓝 0) (𝓝 0) := by
        simpa using hc2.tendsto 0
      have h2' : ∀ᶠ h : ℝ in 𝓝[≠] 0, ‖h • w‖ < ρ :=
        (ht.eventually (gt_mem_nhds hρpos)).filter_mono nhdsWithin_le_nhds
      exact h1'.and h2'
    have hz : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball z₀ ρ := Metric.ball_mem_nhds z₀ hρpos
    have hbound : ∀ z ∈ Metric.ball z₀ ρ, ∀ X ∈ Metric.ball X₀ ρ,
        dist (fderiv ℝ (fun X => H X z) X) (fderiv ℝ (fun X => H X z) X₀) ≤
          2 * (ε / (4 * c)) := by
      intro z hzp X hX
      have hXd : dist (X, z) (X₀, z₀) < δ := by
        rw [Prod.dist_eq, max_lt_iff]
        exact ⟨lt_of_lt_of_le hX (min_le_left _ _), lt_of_lt_of_le hzp (min_le_left _ _)⟩
      have hX0d : dist (X₀, z) (X₀, z₀) < δ := by
        rw [Prod.dist_eq, max_lt_iff]
        exact ⟨by simpa using hδ, lt_of_lt_of_le hzp (min_le_left _ _)⟩
      have e1 := hδc (X, z) hXd
      have e2 := hδc (X₀, z) hX0d
      exact dist_le_two_mul_of_dist_lt e1 e2
    filter_upwards [hh.prod_mk hz] with p hp
    obtain ⟨⟨hh0, hhw⟩, hzp⟩ := hp
    obtain ⟨h, z⟩ := p
    simp only at hh0 hhw hzp ⊢
    have hs := dist_slope_le (K := fun X => H X z) (X₀ := X₀) hρpos
      (fun X hX => (h3 z).differentiableAt (hΩ.mem_nhds (hbΩ hX))) (hbound z hzp) hh0 hhw
    calc _ ≤ 2 * (ε / (4 * c)) * ‖w‖ := hs
      _ < ε := by
        have : ‖w‖ < c := by rw [hc]; linarith
        have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
        calc 2 * (ε / (4 * c)) * ‖w‖ ≤ 2 * (ε / (4 * c)) * c := by gcongr
          _ = ε / 2 := by field_simp; ring
          _ < ε := by linarith
  · -- the difference quotients have the right derivatives
    have hall : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ z, HasFDerivAt
        (fun z => h⁻¹ • (G (X₀ + h • w) z - G X₀ z))
        (h⁻¹ • (H (X₀ + h • w) z - H X₀ z)) z := by
      filter_upwards [hev] with h hh z
      exact ((h1 _ hh z).sub (h1 _ hX₀ z)).const_smul h⁻¹
    exact (hall.prod_inl (𝓝 z₀)).mono fun p hp => hp p.2
  · -- pointwise convergence
    refine Eventually.of_forall fun y => ?_
    have hd : HasFDerivAt (fun X => G X y) (fderiv ℝ (fun X => G X y) X₀) X₀ :=
      ((h2 y).differentiableAt (hΩ.mem_nhds hX₀)).hasFDerivAt
    have h0 : HasDerivAt (fun h : ℝ => X₀ + h • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add X₀
    have hd' : HasFDerivAt (fun X => G X y) (fderiv ℝ (fun X => G X y) X₀) (X₀ + (0 : ℝ) • w) := by
      simpa using hd
    have hl := hd'.comp_hasDerivAt (0 : ℝ) h0
    have := hasDerivAt_iff_tendsto_slope_zero.mp hl
    simpa [Function.comp_def] using this

end AVRegularity.Providers.GenSem
end
end

section
/-! Recursive box data.

`XC Ω a E f`: `f : Vec 2 → Vec 2 → E` is `a` times differentiable in the slow variable on `Ω`,
with all slow derivatives (valued in iterated spaces of continuous linear maps) jointly continuous
on `Ω ×ˢ univ`.  `BoxData Ω a b E f`: the same for all fast derivatives of `f` up to order `b`
(fast derivatives inside, slow derivatives outside). -/

@[expose] public section

open Filter Topology Set Homogenization

universe u

namespace AVRegularity.Providers.GenSem

/-- Slow derivative. -/
noncomputable def DX {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → (Vec 2 →L[ℝ] E) :=
  fun X z => fderiv ℝ (fun X' => f X' z) X

/-- Fast derivative. -/
noncomputable def DZ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → (Vec 2 →L[ℝ] E) :=
  fun X z => fderiv ℝ (f X) z

/-- Slow-variable data up to order `a`. -/
noncomputable def XC (Ω : Set (Vec 2)) : (a : ℕ) → (E : Type u) → [NormedAddCommGroup E] →
    [NormedSpace ℝ E] → (Vec 2 → Vec 2 → E) → Prop
  | 0, _, _, _, f => ContinuousOn (Function.uncurry f) (Ω ×ˢ univ)
  | a + 1, E, _, _, f => ContinuousOn (Function.uncurry f) (Ω ×ˢ univ) ∧
      (∀ z, DifferentiableOn ℝ (fun X => f X z) Ω) ∧ XC Ω a (Vec 2 →L[ℝ] E) (DX f)

/-- Slow data up to order `a`, fast data up to order `b`. -/
noncomputable def BoxData (Ω : Set (Vec 2)) (a : ℕ) : (b : ℕ) → (E : Type u) →
    [NormedAddCommGroup E] → [NormedSpace ℝ E] → (Vec 2 → Vec 2 → E) → Prop
  | 0, E, _, _, f => XC Ω a E f
  | b + 1, E, _, _, f => XC Ω a E f ∧ (∀ X ∈ Ω, ∀ z, DifferentiableAt ℝ (f X) z) ∧
      BoxData Ω a b (Vec 2 →L[ℝ] E) (DZ f)

variable {Ω : Set (Vec 2)} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem XC.cont {a : ℕ} {f : Vec 2 → Vec 2 → E} (h : XC Ω a E f) :
    ContinuousOn (Function.uncurry f) (Ω ×ˢ univ) := by
  cases a with
  | zero => exact h
  | succ a => exact h.1

theorem XC.diff {a : ℕ} {f : Vec 2 → Vec 2 → E} (h : XC Ω (a + 1) E f) (z : Vec 2) :
    DifferentiableOn ℝ (fun X => f X z) Ω := h.2.1 z

theorem XC.dx {a : ℕ} {f : Vec 2 → Vec 2 → E} (h : XC Ω (a + 1) E f) :
    XC Ω a (Vec 2 →L[ℝ] E) (DX f) := h.2.2

theorem XC.mono : ∀ {a a' : ℕ} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec 2 → Vec 2 → E}, a' ≤ a → XC Ω a E f → XC Ω a' E f
  | 0, a', E, _, _, f, ha, h => by
      obtain rfl : a' = 0 := Nat.le_zero.mp ha
      exact h
  | a + 1, a', E, _, _, f, ha, h => by
      cases a' with
      | zero => exact h.cont
      | succ a' => exact ⟨h.1, h.2.1, XC.mono (Nat.le_of_succ_le_succ ha) h.2.2⟩

theorem BoxData.xc : ∀ {b : ℕ} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℕ} {f : Vec 2 → Vec 2 → E}, BoxData Ω a b E f → XC Ω a E f
  | 0, _, _, _, _, _, h => h
  | _ + 1, _, _, _, _, _, h => h.1

theorem BoxData.zd {a b : ℕ} {f : Vec 2 → Vec 2 → E} (h : BoxData Ω a (b + 1) E f) :
    ∀ X ∈ Ω, ∀ z, DifferentiableAt ℝ (f X) z := h.2.1

theorem BoxData.dz {a b : ℕ} {f : Vec 2 → Vec 2 → E} (h : BoxData Ω a (b + 1) E f) :
    BoxData Ω a b (Vec 2 →L[ℝ] E) (DZ f) := h.2.2

section Transfer

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem DX_eq_of_agree (hΩ : IsOpen Ω) {f : Vec 2 → Vec 2 → E} {g : Vec 2 → Vec 2 → F}
    (L : E →L[ℝ] F) (hdiff : ∀ z, DifferentiableOn ℝ (fun X => f X z) Ω)
    (hg : ∀ X ∈ Ω, ∀ z, g X z = L (f X z)) :
    ∀ X ∈ Ω, ∀ z, DX g X z = (ContinuousLinearMap.compL ℝ (Vec 2) E F L) (DX f X z) := by
  intro X hX z
  have hev : (fun X' => g X' z) =ᶠ[𝓝 X] (fun X' => L (f X' z)) :=
    Filter.eventually_of_mem (hΩ.mem_nhds hX) fun X' hX' => hg X' hX' z
  have hd : DifferentiableAt ℝ (fun X' => f X' z) X :=
    (hdiff z).differentiableAt (hΩ.mem_nhds hX)
  unfold DX
  rw [hev.fderiv_eq]
  exact (L.hasFDerivAt.comp X hd.hasFDerivAt).fderiv

theorem XC.transfer (hΩ : IsOpen Ω) : ∀ {a : ℕ} {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Vec 2 → Vec 2 → E} {g : Vec 2 → Vec 2 → F} (L : E →L[ℝ] F),
    XC Ω a E f → (∀ X ∈ Ω, ∀ z, g X z = L (f X z)) → XC Ω a F g
  | 0, E, _, _, F, _, _, f, g, L, h, hg => by
      have : ContinuousOn (fun p : Vec 2 × Vec 2 => L (f p.1 p.2)) (Ω ×ˢ univ) :=
        L.continuous.comp_continuousOn h
      exact this.congr fun p hp => hg p.1 hp.1 p.2
  | a + 1, E, _, _, F, _, _, f, g, L, h, hg => by
      refine ⟨?_, ?_, ?_⟩
      · have : ContinuousOn (fun p : Vec 2 × Vec 2 => L (f p.1 p.2)) (Ω ×ˢ univ) :=
          L.continuous.comp_continuousOn h.cont
        exact this.congr fun p hp => hg p.1 hp.1 p.2
      · intro z
        exact (L.differentiable.comp_differentiableOn (h.diff z)).congr fun X hX => hg X hX z
      · exact XC.transfer hΩ (ContinuousLinearMap.compL ℝ (Vec 2) E F L) h.dx
          (DX_eq_of_agree hΩ L h.diff hg)

theorem BoxData.transfer (hΩ : IsOpen Ω) : ∀ {b : ℕ} {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {a : ℕ}
    {f : Vec 2 → Vec 2 → E} {g : Vec 2 → Vec 2 → F} (L : E →L[ℝ] F),
    BoxData Ω a b E f → (∀ X ∈ Ω, ∀ z, g X z = L (f X z)) → BoxData Ω a b F g
  | 0, E, _, _, F, _, _, a, f, g, L, h, hg => XC.transfer hΩ L h hg
  | b + 1, E, _, _, F, _, _, a, f, g, L, h, hg => by
      refine ⟨XC.transfer hΩ L h.1 hg, ?_, ?_⟩
      · intro X hX z
        have hgX : g X = fun z => L (f X z) := funext (hg X hX)
        rw [hgX]
        exact L.differentiableAt.comp z (h.zd X hX z)
      · refine BoxData.transfer hΩ (ContinuousLinearMap.compL ℝ (Vec 2) E F L) h.dz ?_
        intro X hX z
        have hgX : g X = fun z => L (f X z) := funext (hg X hX)
        unfold DZ
        rw [hgX]
        exact (L.hasFDerivAt.comp z (h.zd X hX z).hasFDerivAt).fderiv

end Transfer

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public section
open Filter Topology Set
namespace AVRegularity.Providers.GenSem

/-! Interchange of the slow and fast derivatives, operator-valued form: the slow derivative of
`G` is fast-differentiable with derivative the flipped slow derivative of the fast derivative. -/

variable {Z E : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFDerivAt_slowDeriv_of_mixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω)
    {G : (ι → ℝ) → Z → E} {H : (ι → ℝ) → Z → (Z →L[ℝ] E)}
    (h1 : ∀ X ∈ Ω, ∀ z, HasFDerivAt (G X) (H X z) z)
    (h2 : ∀ z, DifferentiableOn ℝ (fun X => G X z) Ω)
    (h3 : ∀ z, DifferentiableOn ℝ (fun X => H X z) Ω)
    (h4 : ContinuousOn (fun p : (ι → ℝ) × Z => fderiv ℝ (fun X => H X p.2) p.1)
      (Ω ×ˢ Set.univ))
    {X₀ : ι → ℝ} (hX₀ : X₀ ∈ Ω) (z₀ : Z) :
    HasFDerivAt (fun z => fderiv ℝ (fun X => G X z) X₀)
      (fderiv ℝ (fun X => H X z₀) X₀).flip z₀ := by
  let e : ((ι → ℝ) →L[ℝ] E) ≃L[ℝ] (ι → E) := ContinuousLinearEquiv.piRing ι
  rw [← e.comp_hasFDerivAt_iff]
  refine hasFDerivAt_pi'.2 fun i => ?_
  have := hasFDerivAt_slowDirDeriv_of_mixed hΩ h1 h2 h3 h4 hX₀ (Pi.single i 1) z₀
  show HasFDerivAt (fun z => fderiv ℝ (fun X => G X z) X₀ (Pi.single i 1)) _ z₀
  convert this using 1
  ext v
  rfl

end AVRegularity.Providers.GenSem
end
end

section
/-! A slow derivative can be taken outside all fast derivatives: `BoxData (a+1) b f` implies
`BoxData a b (DX f)`. -/

@[expose] public section

open Filter Topology Set Homogenization

universe u

namespace AVRegularity.Providers.GenSem

variable {Ω : Set (Vec 2)}

theorem BoxData.swap (hΩ : IsOpen Ω) : ∀ {b : ℕ} {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℕ} {f : Vec 2 → Vec 2 → E},
    BoxData Ω (a + 1) b E f → BoxData Ω a b (Vec 2 →L[ℝ] E) (DX f)
  | 0, E, _, _, a, f, h => XC.dx h
  | b + 1, E, _, _, a, f, h => by
      have hZ := h.dz
      have ih := BoxData.swap hΩ hZ
      have hA : ∀ X₀ ∈ Ω, ∀ z₀, HasFDerivAt (DX f X₀)
          (fderiv ℝ (fun X => DZ f X z₀) X₀).flip z₀ := fun X₀ hX₀ z₀ =>
        hasFDerivAt_slowDeriv_of_mixed hΩ (G := f) (H := DZ f)
          (fun X hX z => (h.zd X hX z).hasFDerivAt) h.xc.diff hZ.xc.diff
          hZ.xc.dx.cont hX₀ z₀
      refine ⟨h.xc.dx, fun X hX z => (hA X hX z).differentiableAt, ?_⟩
      refine BoxData.transfer hΩ
        ((ContinuousLinearMap.flipₗᵢ ℝ (Vec 2) (Vec 2) E).toContinuousLinearEquiv.toContinuousLinearMap)
        ih ?_
      intro X hX z
      exact (hA X hX z).fderiv

end AVRegularity.Providers.GenSem
end
end

section
/-! Recursive box data of orders at least `R` gives joint `C^R` regularity. -/

@[expose] public section

open Filter Topology Set Homogenization

universe u

namespace AVRegularity.Providers.GenSem

variable {Ω : Set (Vec 2)}

theorem BoxData.hasFDerivAt_uncurry {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hΩ : IsOpen Ω) {a b : ℕ} {f : Vec 2 → Vec 2 → E}
    (h : BoxData Ω (a + 1) (b + 1) E f) (p : Vec 2 × Vec 2) (hp : p ∈ Ω ×ˢ (univ : Set (Vec 2))) :
    HasFDerivAt (Function.uncurry f) ((DX f p.1 p.2).coprod (DZ f p.1 p.2)) p := by
  have hO : IsOpen (Ω ×ˢ (univ : Set (Vec 2))) := hΩ.prod isOpen_univ
  have hX : BoxData Ω a (b + 1) (Vec 2 →L[ℝ] E) (DX f) := BoxData.swap hΩ h
  have hZ : BoxData Ω (a + 1) b (Vec 2 →L[ℝ] E) (DZ f) := h.dz
  have hs := hasStrictFDerivAt_uncurry_coprod (u := p) (f := f) (f₁ := DX f) (f₂ := DZ f)
    (Filter.eventually_of_mem (hO.mem_nhds hp) fun v hv =>
      ((h.xc.diff v.2).differentiableAt (hΩ.mem_nhds hv.1)).hasFDerivAt)
    (Filter.eventually_of_mem (hO.mem_nhds hp) fun v hv =>
      (h.zd v.1 hv.1 v.2).hasFDerivAt)
    (hX.xc.cont.continuousAt (hO.mem_nhds hp)) (hZ.xc.cont.continuousAt (hO.mem_nhds hp))
  exact hs.hasFDerivAt

theorem BoxData.contDiffOn (hΩ : IsOpen Ω) : ∀ (R : ℕ) {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℕ} {f : Vec 2 → Vec 2 → E}, R ≤ a → R ≤ b → BoxData Ω a b E f →
    ContDiffOn ℝ (R : WithTop ℕ∞) (Function.uncurry f) (Ω ×ˢ (univ : Set (Vec 2)))
  | 0, E, _, _, a, b, f, _, _, h => by
      rw [Nat.cast_zero, contDiffOn_zero]
      exact h.xc.cont
  | R + 1, E, _, _, a, b, f, ha, hb, h => by
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have hO : IsOpen (Ω ×ˢ (univ : Set (Vec 2))) := hΩ.prod isOpen_univ
      have hX : BoxData Ω a' (b' + 1) (Vec 2 →L[ℝ] E) (DX f) := BoxData.swap hΩ h
      have hZ : BoxData Ω (a' + 1) b' (Vec 2 →L[ℝ] E) (DZ f) := h.dz
      have ihX := BoxData.contDiffOn hΩ R (by omega) (by omega) hX
      have ihZ := BoxData.contDiffOn hΩ R (by omega) (by omega) hZ
      have hder := BoxData.hasFDerivAt_uncurry hΩ h
      have hcast : ((R + 1 : ℕ) : WithTop ℕ∞) = (R : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hO]
      refine ⟨fun p hp => (hder p hp).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · intro h'
        exact absurd h' (by simp)
      · let Φ : ((Vec 2 →L[ℝ] E) × (Vec 2 →L[ℝ] E)) ≃L[ℝ] (Vec 2 × Vec 2 →L[ℝ] E) :=
          ContinuousLinearMap.coprodEquivL ℝ
        have hC : ContDiffOn ℝ (R : WithTop ℕ∞)
            (fun p : Vec 2 × Vec 2 => Φ ((DX f p.1 p.2), (DZ f p.1 p.2))) (Ω ×ˢ univ) :=
          Φ.contDiff.comp_contDiffOn (ihX.prodMk ihZ)
        exact hC.congr fun p hp => (hder p hp).fderiv.trans rfl

end AVRegularity.Providers.GenSem
end
end

section
/-! `IsBoxSmoothOn` gives the recursive box data. -/

@[expose] public section

open Filter Topology Set Homogenization

universe u

namespace AVRegularity.Providers.GenSem

variable {Ω : Set (Vec 2)}

/-- Slow-variable part of the box data, in `iteratedFDeriv` form. -/
def XBox {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : Set (Vec 2)) (a : ℕ)
    (f : Vec 2 → Vec 2 → E) : Prop :=
  (∀ z, ContDiffOn ℝ (a : ℕ∞) (fun X => f X z) Ω) ∧
  ∀ a', a' ≤ a → ContinuousOn (fun p : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ a' (fun X' => f X' p.2) p.1) (Ω ×ˢ Set.univ)

section Equiv

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

theorem continuousOn_iteratedFDeriv_equiv (e : F ≃L[ℝ] G) {φ : Vec 2 → Vec 2 → F}
    {ψ : Vec 2 → Vec 2 → G} (hψ : ∀ X z, ψ X z = e (φ X z)) (a' : ℕ)
    (h : ContinuousOn (fun p : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ a' (fun X' => φ X' p.2) p.1) (Ω ×ˢ Set.univ)) :
    ContinuousOn (fun p : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ a' (fun X' => ψ X' p.2) p.1) (Ω ×ˢ Set.univ) := by
  have hfun : ∀ p : Vec 2 × Vec 2, iteratedFDeriv ℝ a' (fun X' => ψ X' p.2) p.1 =
      e.toContinuousLinearMap.compContinuousMultilinearMap
        (iteratedFDeriv ℝ a' (fun X' => φ X' p.2) p.1) := by
    intro p
    have : (fun X' => ψ X' p.2) = e ∘ (fun X' => φ X' p.2) := funext fun X' => hψ X' p.2
    rw [this, e.iteratedFDeriv_comp_left]
  simp_rw [hfun]
  exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin a' => Vec 2) F G
    e.toContinuousLinearMap).continuous).comp_continuousOn h

end Equiv

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem xbox_of_box {a b : ℕ} {f : Vec 2 → Vec 2 → E} (h : IsBoxSmoothOn Ω a b f) :
    XBox Ω a f := by
  let e : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Vec 2) E ≃L[ℝ] E :=
    (continuousMultilinearCurryFin0 ℝ (Vec 2) E).toContinuousLinearEquiv
  have hψ : ∀ X z, f X z = e (iteratedFDeriv ℝ 0 (f X) z) := by
    intro X z
    rw [iteratedFDeriv_zero_eq_comp]
    simp [e]
  refine ⟨fun z => ?_, fun a' ha' => ?_⟩
  · exact (e.contDiff.comp_contDiffOn (h.2.1 0 (Nat.zero_le _) z)).congr fun X _ => hψ X z
  · exact continuousOn_iteratedFDeriv_equiv e hψ a' (h.2.2 a' 0 ha' (Nat.zero_le b))

theorem XBox.dx {a : ℕ} {f : Vec 2 → Vec 2 → E} (hΩ : IsOpen Ω) (h : XBox Ω (a + 1) f) :
    XBox Ω a (DX f) := by
  refine ⟨fun z => ?_, fun a' ha' => ?_⟩
  · exact (h.1 z).fderiv_of_isOpen hΩ (by exact_mod_cast le_rfl)
  · let e : ContinuousMultilinearMap ℝ (fun _ : Fin (a' + 1) => Vec 2) E ≃L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin a' => Vec 2) (Vec 2 →L[ℝ] E) :=
      (continuousMultilinearCurryRightEquiv' ℝ a' (Vec 2) E).symm.symm.toContinuousLinearEquiv
    have hc := e.continuous.comp_continuousOn (h.2 (a' + 1) (by omega))
    refine hc.congr fun p _ => ?_
    simp only [Function.comp_apply]
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp [e, DX]

theorem XBox.cont {a : ℕ} {f : Vec 2 → Vec 2 → E} (h : XBox Ω a f) :
    ContinuousOn (Function.uncurry f) (Ω ×ˢ (univ : Set (Vec 2))) := by
  have h0 := h.2 0 (Nat.zero_le a)
  let e : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Vec 2) E ≃L[ℝ] E :=
    (continuousMultilinearCurryFin0 ℝ (Vec 2) E).toContinuousLinearEquiv
  have := e.continuous.comp_continuousOn h0
  refine this.congr fun p _ => ?_
  simp only [Function.comp_apply]
  rw [iteratedFDeriv_zero_eq_comp]
  simp [e, Function.uncurry]

theorem XBox.xc (hΩ : IsOpen Ω) : ∀ {a : ℕ} {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Vec 2 → Vec 2 → E}, XBox Ω a f → XC Ω a E f
  | 0, E, _, _, f, h => h.cont
  | a + 1, E, _, _, f, h =>
      ⟨h.cont, fun z => (h.1 z).differentiableOn (by exact_mod_cast Nat.succ_ne_zero a),
        XBox.xc hΩ (h.dx hΩ)⟩

theorem box_dz {a b : ℕ} {f : Vec 2 → Vec 2 → E} (h : IsBoxSmoothOn Ω a (b + 1) f) :
    IsBoxSmoothOn Ω a b (DZ f) := by
  have hψ : ∀ (b' : ℕ) (X z : Vec 2), iteratedFDeriv ℝ b' (DZ f X) z =
      (continuousMultilinearCurryRightEquiv' ℝ b' (Vec 2) E).symm.symm.toContinuousLinearEquiv
        (iteratedFDeriv ℝ (b' + 1) (f X) z) := by
    intro b' X z
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp
    rfl
  refine ⟨fun X hX => ?_, fun b' hb' z => ?_, fun a' b' ha' hb' => ?_⟩
  · exact (h.1 X hX).fderiv_right (by exact_mod_cast le_rfl)
  · exact (ContinuousLinearEquiv.contDiff _ |>.comp_contDiffOn
      (h.2.1 (b' + 1) (by omega) z)).congr fun X _ => hψ b' X z
  · exact continuousOn_iteratedFDeriv_equiv
      (continuousMultilinearCurryRightEquiv' ℝ b' (Vec 2) E).symm.symm.toContinuousLinearEquiv
      (φ := fun X z => iteratedFDeriv ℝ (b' + 1) (f X) z) (hψ b') a'
      (h.2.2 a' (b' + 1) ha' (by omega))

theorem BoxData.of_box (hΩ : IsOpen Ω) : ∀ {b : ℕ} {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℕ} {f : Vec 2 → Vec 2 → E}, IsBoxSmoothOn Ω a b f →
    BoxData Ω a b E f
  | 0, E, _, _, a, f, h => XBox.xc hΩ (xbox_of_box h)
  | b + 1, E, _, _, a, f, h =>
      ⟨XBox.xc hΩ (xbox_of_box h),
        fun X hX z => ((h.1 X hX).differentiable (by exact_mod_cast Nat.succ_ne_zero b)) z,
        BoxData.of_box hΩ (box_dz h)⟩

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public section
open Set Homogenization
namespace AVRegularity.Providers.GenSem

/-! Box regularity (fast derivatives inside, slow derivatives outside, all continuous) implies
joint regularity on `Ω ×ˢ univ`. -/

theorem IsBoxSmoothOn.contDiffOn_uncurry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set (Vec 2)} (hΩ : IsOpen Ω) {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmoothOn Ω sX sZ f) {R : ℕ} (hRX : R ≤ sX) (hRZ : R ≤ sZ) :
    ContDiffOn ℝ (R : WithTop ℕ∞) (Function.uncurry f) (Ω ×ˢ Set.univ) :=
  BoxData.contDiffOn hΩ R hRX hRZ (BoxData.of_box hΩ hf)

end AVRegularity.Providers.GenSem
end
end
