-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.QuietDecay.Engine.DiffConv
import AVRegularity.Analysis.Convolution.Kernel.Commutation.Torus
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsCellSolution
public import AVRegularity.Analysis.Convolution.Kernel.Spatial

@[expose] public noncomputable section

section
open MeasureTheory Homogenization
open AVenhance.Infra.Torus
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Translation of periodic functions on the cube: a periodic function translated by `w`
equals the function composed with a measure-preserving self-map of the cube. -/

/-- The self-map of the cube induced by translation by `w` on the torus. -/
def cubeShift (w : Vec 2) : Vec 2 → Vec 2 :=
  fun z => unitTorusRepresentative 2 (torusQuotient z + torusQuotient w)

theorem measurePreserving_cubeShift (w : Vec 2) :
    MeasurePreserving (cubeShift w) (volume.restrict AVenhance.unitCube)
      (volume.restrict AVenhance.unitCube) := by
  have h1 := measurePreserving_torusQuotient_cell
  have h2 := measurePreserving_add_right torusMeasure (torusQuotient w)
  have h3 := measurePreserving_unitTorusRepresentative_cell
  exact h3.comp (h2.comp h1)

theorem periodic_add_eq_cubeShift {β : Type*} {g : Vec 2 → β} (hp : AVenhance.IsZ2Periodic g)
    (w z : Vec 2) : g (z + w) = g (cubeShift w z) := by
  unfold cubeShift
  rw [← map_add, periodic_eq_rep hp]

variable {β : Type*}

theorem lintegral_shift {g : Vec 2 → ℝ≥0∞} (hp : AVenhance.IsZ2Periodic g)
    (hg : AEMeasurable g (volume.restrict AVenhance.unitCube)) (w : Vec 2) :
    ∫⁻ z in AVenhance.unitCube, g (z + w) = ∫⁻ z in AVenhance.unitCube, g z := by
  have hmp := measurePreserving_cubeShift w
  have h := lintegral_map' (μ := volume.restrict AVenhance.unitCube)
    (by rwa [hmp.map_eq]) hmp.aemeasurable
  rw [hmp.map_eq] at h
  rw [h]
  exact lintegral_congr fun z => periodic_add_eq_cubeShift hp w z

theorem integral_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Vec 2 → E}
    (hp : AVenhance.IsZ2Periodic g)
    (hg : AEStronglyMeasurable g (volume.restrict AVenhance.unitCube)) (w : Vec 2) :
    ∫ z in AVenhance.unitCube, g (z + w) = ∫ z in AVenhance.unitCube, g z := by
  have hmp := measurePreserving_cubeShift w
  have h := integral_map (μ := volume.restrict AVenhance.unitCube)
    hmp.aemeasurable (by rwa [hmp.map_eq]) (f := g)
  rw [hmp.map_eq] at h
  rw [h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => periodic_add_eq_cubeShift hp w z)

theorem memLp_shift {E : Type*} [NormedAddCommGroup E] {g : Vec 2 → E} {p : ℝ≥0∞}
    (hp : AVenhance.IsZ2Periodic g)
    (hg : MemLp g p (volume.restrict AVenhance.unitCube)) (w : Vec 2) :
    MemLp (fun z => g (z + w)) p (volume.restrict AVenhance.unitCube) :=
  (hg.comp_measurePreserving (measurePreserving_cubeShift w)).ae_eq
    (Filter.Eventually.of_forall fun z => (periodic_add_eq_cubeShift hp w z).symm)

theorem integrable_shift {E : Type*} [NormedAddCommGroup E] {g : Vec 2 → E}
    (hp : AVenhance.IsZ2Periodic g)
    (hg : Integrable g (volume.restrict AVenhance.unitCube)) (w : Vec 2) :
    Integrable (fun z => g (z + w)) (volume.restrict AVenhance.unitCube) :=
  memLp_one_iff_integrable.mp (memLp_shift hp (memLp_one_iff_integrable.mpr hg) w)

theorem eLpNorm_shift {E : Type*} [NormedAddCommGroup E] {g : Vec 2 → E} {p : ℝ≥0∞}
    (hp : AVenhance.IsZ2Periodic g)
    (hg : AEStronglyMeasurable g (volume.restrict AVenhance.unitCube)) (w : Vec 2) :
    eLpNorm (fun z => g (z + w)) p (volume.restrict AVenhance.unitCube) =
      eLpNorm g p (volume.restrict AVenhance.unitCube) := by
  rw [← eLpNorm_comp_measurePreserving hg (measurePreserving_cubeShift w)]
  exact eLpNorm_congr_ae (Filter.Eventually.of_forall fun z => periodic_add_eq_cubeShift hp w z)

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization
namespace AVRegularity.QuietDecay

/-! Joint a.e. strong measurability of translated time-dependent periodic families. -/

theorem aestronglyMeasurable_joint_shift {I : Set ℝ} {f : ℝ → Vec 2 → ℂ}
    (hf : AEStronglyMeasurable (fun p : ℝ × Vec 2 => f p.1 p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hper : ∀ᵐ t ∂(volume.restrict I), AVenhance.IsZ2Periodic (f t)) (w : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => f p.1 (p.2 + w))
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  have hmp : MeasurePreserving (Prod.map id (cubeShift w))
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) :=
    (MeasurePreserving.id (volume.restrict I)).prod (measurePreserving_cubeShift w)
  have h := hf.comp_measurePreserving hmp
  refine h.congr ?_
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict I)
    (ν := volume.restrict AVenhance.unitCube)).ae hper
  filter_upwards [hfst] with p hp
  exact (periodic_add_eq_cubeShift hp w p.2).symm

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.QuietDecay

/-! Translating periodic ordered weak jets (and `H¹` test functions) by a vector. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasOrderedWeakJetOn_translate {K : ℕ} {D : RawJet2 K E}
    (h : HasOrderedWeakJetOn Set.univ D) (w : Vec 2) :
    HasOrderedWeakJetOn Set.univ (fun a x => D a (x + w)) := by
  intro j wd i e
  have := AVRegularity.Analysis.Convolution.hasWeakPartialDerivOn_translate_univ
    (h j wd i e) (-w)
  simpa only [sub_neg_eq_add] using this

theorem hasPeriodicOrderedWeakJet_translate {K : ℕ} {D : RawJet2 K E}
    (h : HasPeriodicOrderedWeakJet D) (w : Vec 2) :
    HasPeriodicOrderedWeakJet (fun a x => D a (x + w)) := by
  obtain ⟨hp, hm, hw⟩ := h
  refine ⟨fun a n x => ?_, fun a => memLp_shift (hp a) (hm a) w, hasOrderedWeakJetOn_translate hw w⟩
  show D a (x + AVenhance.latticeShift n + w) = D a (x + w)
  rw [show x + AVenhance.latticeShift n + w = x + w + AVenhance.latticeShift n by abel]
  exact hp a n (x + w)

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization
namespace AVRegularity.QuietDecay

/-! Translation invariance of the cell weak identity for space-independent coefficients. -/

/-- The integrand of `CellWeakIdentity`, as a named function. -/
def cellRhs (C : CellCoefficients) (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (τ : ℝ) (x : Vec 2) : ℂ :=
  -(∑ j : Fin 2, ∑ k : Fin 2, (C.G τ x j k : ℂ) *
        (du τ j x + Complex.I * C.θ j * u τ x) * (dψ k x - Complex.I * C.θ k * ψ x))
      - ∑ k : Fin 2, (C.v τ x k : ℂ) * (du τ k x + Complex.I * C.θ k * u τ x) * ψ x
      + C.κ τ * u τ x * ψ x + src τ x * ψ x
      - ∑ k : Fin 2, F τ x k * (dψ k x - Complex.I * C.θ k * ψ x)

theorem cellWeakIdentity_iff (C : CellCoefficients) (s t : ℝ) (u₀ u₁ ψ : Vec 2 → ℂ)
    (dψ : Fin 2 → Vec 2 → ℂ) (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) :
    CellWeakIdentity C s t u₀ u₁ ψ dψ u du src F ↔
      (Integrable (fun x => u₁ x * ψ x) (volume.restrict AVenhance.unitCube) ∧
      Integrable (fun x => u₀ x * ψ x) (volume.restrict AVenhance.unitCube) ∧
      (∀ᵐ τ ∂(volume.restrict (Set.Ioc s t)),
        Integrable (cellRhs C u du ψ dψ src F τ) (volume.restrict AVenhance.unitCube)) ∧
      IntegrableOn (fun τ => ∫ x, cellRhs C u du ψ dψ src F τ x
        ∂(volume.restrict AVenhance.unitCube)) (Set.Ioc s t) ∧
      ∫ x, u₁ x * ψ x ∂(volume.restrict AVenhance.unitCube) -
        ∫ x, u₀ x * ψ x ∂(volume.restrict AVenhance.unitCube) =
        ∫ τ in Set.Ioc s t, ∫ x, cellRhs C u du ψ dψ src F τ x
          ∂(volume.restrict AVenhance.unitCube)) := Iff.rfl

section
variable (C : CellCoefficients) (hG : ∀ τ x y, C.G τ x = C.G τ y)
  (hv : ∀ τ x y, C.v τ x = C.v τ y)

include hG hv in
theorem cellRhs_shift (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (w : Vec 2) (τ : ℝ) (x : Vec 2) :
    cellRhs C (fun τ z => u τ (z + w)) (fun τ k z => du τ k (z + w)) (fun z => ψ (z + w))
      (fun k z => dψ k (z + w)) (fun τ z => src τ (z + w)) (fun τ z => F τ (z + w)) τ x =
      cellRhs C u du ψ dψ src F τ (x + w) := by
  simp only [cellRhs, hG τ (x + w) x, hv τ (x + w) x]

include hG hv in
theorem cellRhs_periodic (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (τ : ℝ)
    (hu : AVenhance.IsZ2Periodic (u τ)) (hdu : ∀ k, AVenhance.IsZ2Periodic (du τ k))
    (hψ : AVenhance.IsZ2Periodic ψ) (hdψ : ∀ k, AVenhance.IsZ2Periodic (dψ k))
    (hs : AVenhance.IsZ2Periodic (src τ)) (hF : AVenhance.IsZ2Periodic (F τ)) :
    AVenhance.IsZ2Periodic (cellRhs C u du ψ dψ src F τ) := by
  intro n x
  simp only [cellRhs, hG τ (x + AVenhance.latticeShift n) x, hv τ (x + AVenhance.latticeShift n) x,
    hu n x, hdu _ n x, hψ n x, hdψ _ n x, hs n x, hF n x]

include hG hv in
theorem cellWeakIdentity_translate {s t : ℝ} {u₀ u₁ ψ : Vec 2 → ℂ}
    {dψ : Fin 2 → Vec 2 → ℂ} {u : ℝ → Vec 2 → ℂ} {du : ℝ → Fin 2 → Vec 2 → ℂ}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (hu₀ : AVenhance.IsZ2Periodic u₀) (hu₁ : AVenhance.IsZ2Periodic u₁)
    (hψ : AVenhance.IsZ2Periodic ψ) (hdψ : ∀ k, AVenhance.IsZ2Periodic (dψ k))
    (hu : ∀ τ ∈ Set.Ioc s t, AVenhance.IsZ2Periodic (u τ))
    (hdu : ∀ᵐ τ ∂(volume.restrict (Set.Ioc s t)), ∀ k, AVenhance.IsZ2Periodic (du τ k))
    (hsrc : ∀ τ ∈ Set.Ioc s t, AVenhance.IsZ2Periodic (src τ))
    (hF : ∀ τ ∈ Set.Ioc s t, AVenhance.IsZ2Periodic (F τ))
    (h : CellWeakIdentity C s t u₀ u₁ ψ dψ u du src F) (w : Vec 2) :
    CellWeakIdentity C s t (fun z => u₀ (z + w)) (fun z => u₁ (z + w)) (fun z => ψ (z + w))
      (fun k z => dψ k (z + w)) (fun τ z => u τ (z + w)) (fun τ k z => du τ k (z + w))
      (fun τ z => src τ (z + w)) (fun τ z => F τ (z + w)) := by
  rw [cellWeakIdentity_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hper : ∀ᵐ τ ∂(volume.restrict (Set.Ioc s t)),
      AVenhance.IsZ2Periodic (cellRhs C u du ψ dψ src F τ) := by
    filter_upwards [hdu, ae_restrict_mem measurableSet_Ioc] with τ hd hτ
    exact cellRhs_periodic C hG hv u du ψ dψ src F τ (hu τ hτ) hd hψ hdψ (hsrc τ hτ) (hF τ hτ)
  have hpt : (fun τ x => cellRhs C (fun τ z => u τ (z + w)) (fun τ k z => du τ k (z + w))
      (fun z => ψ (z + w)) (fun k z => dψ k (z + w)) (fun τ z => src τ (z + w))
      (fun τ z => F τ (z + w)) τ x) =
      fun τ x => cellRhs C u du ψ dψ src F τ (x + w) := by
    funext τ x; exact cellRhs_shift C hG hv u du ψ dψ src F w τ x
  have hint : (fun τ => ∫ x, cellRhs C (fun τ z => u τ (z + w)) (fun τ k z => du τ k (z + w))
      (fun z => ψ (z + w)) (fun k z => dψ k (z + w)) (fun τ z => src τ (z + w))
      (fun τ z => F τ (z + w)) τ x ∂(volume.restrict AVenhance.unitCube)) =ᵐ[
        volume.restrict (Set.Ioc s t)]
      fun τ => ∫ x, cellRhs C u du ψ dψ src F τ x ∂(volume.restrict AVenhance.unitCube) := by
    filter_upwards [hper, h3] with τ hp hi
    rw [show (fun x => cellRhs C (fun τ z => u τ (z + w)) (fun τ k z => du τ k (z + w))
      (fun z => ψ (z + w)) (fun k z => dψ k (z + w)) (fun τ z => src τ (z + w))
      (fun τ z => F τ (z + w)) τ x) = fun x => cellRhs C u du ψ dψ src F τ (x + w) from
        congrFun hpt τ]
    exact integral_shift hp hi.aestronglyMeasurable w
  refine ⟨integrable_shift (g := fun x => u₁ x * ψ x) (fun n x => by
      simp only [hu₁ n x, hψ n x]) h1 w, integrable_shift (g := fun x => u₀ x * ψ x)
      (fun n x => by simp only [hu₀ n x, hψ n x]) h2 w, ?_, ?_, ?_⟩
  · filter_upwards [hper, h3] with τ hp hi
    exact (integrable_shift hp hi w).congr (Filter.Eventually.of_forall fun x =>
      (cellRhs_shift C hG hv u du ψ dψ src F w τ x).symm)
  · exact h4.congr_fun_ae hint.symm
  · rw [integral_shift (g := fun x => u₁ x * ψ x) (fun n x => by simp only [hu₁ n x, hψ n x])
      h1.aestronglyMeasurable w, integral_shift (g := fun x => u₀ x * ψ x)
      (fun n x => by simp only [hu₀ n x, hψ n x]) h2.aestronglyMeasurable w, h5]
    exact (integral_congr_ae hint).symm

end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.QuietDecay

/-! Translation invariance of cell solutions in the fast variable when the cell coefficients
do not depend on the fast variable. -/

theorem cellGradient_aestronglyMeasurable {D : RawJet2 1 ℂ}
    (h : ∀ k, AEStronglyMeasurable (cellGradComp D k)
      (volume.restrict AVenhance.unitCube)) :
    AEStronglyMeasurable (cellGradient D) (volume.restrict AVenhance.unitCube) := by
  have h1 : AEStronglyMeasurable (fun x k => cellGradComp D k x)
      (volume.restrict AVenhance.unitCube) := (aemeasurable_pi_iff.mpr fun k => (h k).aemeasurable).aestronglyMeasurable
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp_aestronglyMeasurable h1

theorem cellL2Norm_gradient_shift {D : RawJet2 1 ℂ} (hD : HasPeriodicOrderedWeakJet D) (w : Vec 2) :
    cellL2Norm (cellGradient (fun a z => D a (z + w))) = cellL2Norm (cellGradient D) := by
  have hp : AVenhance.IsZ2Periodic (cellGradient D) := fun n x => by
    change WithLp.toLp 2 (fun k => cellGradComp D k (x + AVenhance.latticeShift n)) =
      WithLp.toLp 2 (fun k => cellGradComp D k x)
    simp only [cellGradComp, hD.1 _ n x]
  have hm := cellGradient_aestronglyMeasurable (D := D) fun k => (hD.2.1 _).aestronglyMeasurable
  exact eLpNorm_shift hp hm w

theorem cellSolution_translate {I : Set ℝ} (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2) (κ : ℝ → ℂ) {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hsrc : ∀ t ∈ I, AVenhance.IsZ2Periodic (src t))
    (hF : ∀ t ∈ I, AVenhance.IsZ2Periodic (F t))
    (h : IsCellSolution I ⟨fun t _ => G t, fun t _ => v t, 0, κ⟩ src F D) (w : Vec 2) :
    IsCellSolution I ⟨fun t _ => G t, fun t _ => v t, 0, κ⟩ (fun t z => src t (z + w))
      (fun t z => F t (z + w)) (fun t a z => D t a (z + w)) := by
  obtain ⟨hI, hjet, hval, hmeas, hcont, hgrad, hweak⟩ := h
  have hper_ae : ∀ᵐ t ∂(volume.restrict I), ∀ a, AVenhance.IsZ2Periodic (D t a) :=
    hjet.mono fun t ht => ht.1
  refine ⟨hI, hjet.mono fun t ht => hasPeriodicOrderedWeakJet_translate ht w, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨memLp_shift (hval t ht).2 (hval t ht).1 w, fun n x => ?_⟩
    change cellValue D t (x + AVenhance.latticeShift n + w) = cellValue D t (x + w)
    rw [add_right_comm]
    exact (hval t ht).2 n (x + w)
  · intro a
    exact aestronglyMeasurable_joint_shift (f := fun t => D t a) (hmeas a)
      (hper_ae.mono fun t ht => ht a) w
  · intro t₀ ht₀
    refine (hcont t₀ ht₀).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hp : AVenhance.IsZ2Periodic (fun x => cellValue D t x - cellValue D t₀ x) := fun n x => by
      simp only [(hval t ht).2 n x, (hval t₀ ht₀).2 n x]
    have hm : AEMeasurable (fun x => ‖cellValue D t x - cellValue D t₀ x‖ₑ ^ 2)
        (volume.restrict AVenhance.unitCube) :=
      (((hval t ht).1.aestronglyMeasurable.sub (hval t₀ ht₀).1.aestronglyMeasurable).enorm).pow_const 2
    exact (lintegral_shift (g := fun x => ‖cellValue D t x - cellValue D t₀ x‖ₑ ^ 2)
      (fun n x => by simp only [(hval t ht).2 n x, (hval t₀ ht₀).2 n x]) hm w).symm
  · intro a ha b hb
    have hsub : Set.Icc a b ⊆ I := hI.out ha hb
    rw [lintegral_congr_ae (g := fun τ => cellL2Norm (cellGradient (D τ)) ^ 2)]
    · exact hgrad a ha b hb
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hjet] with τ hτ
      rw [show cellGradient (fun a z => D τ a (z + w)) = _ from rfl]
      simp only [cellL2Norm_gradient_shift hτ w]
  · intro s hs t ht hst ψ
    have hsub : Set.Ioc s t ⊆ I := fun τ hτ => hI.out hs ht ⟨hτ.1.le, hτ.2⟩
    let ψ' : TorusHkFunction 1 ℂ :=
      ⟨fun a x => ψ.jet a (x + -w), hasPeriodicOrderedWeakJet_translate ψ.hasPeriodicWeakJet (-w)⟩
    have h1 := hweak s hs t ht hst ψ'
    have h2 := cellWeakIdentity_translate (C := ⟨fun t _ => G t, fun t _ => v t, 0, κ⟩)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) (hval s hs).2 (hval t ht).2
      (ψ'.hasPeriodicWeakJet.1 _) (fun k => ψ'.hasPeriodicWeakJet.1 _)
      (fun τ hτ => (hval τ (hsub hτ)).2)
      (ae_restrict_of_ae_restrict_of_subset hsub (hjet.mono fun τ hτ k => hτ.1 _))
      (fun τ hτ => hsrc τ (hsub hτ)) (fun τ hτ => hF τ (hsub hτ)) h1 w
    simp only [ψ', add_neg_cancel_right] at h2
    exact h2

end AVRegularity.QuietDecay
end
