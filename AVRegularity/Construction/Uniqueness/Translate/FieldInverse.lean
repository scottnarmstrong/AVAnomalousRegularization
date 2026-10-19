-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PlaneScalarDiffusionDeviationReadout
public import AVRegularity.Construction.Uniqueness.CellFieldUnique

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVenhance.Infra.Torus
open scoped ENNReal
namespace AVRegularity.Uniqueness.Translate

/-! Translation invariance of cell integrals of `ℤ²`-periodic functions: for a periodic `f` and
any shift `a : Vec 2`, the integral, `L²` norm, integrability and a.e. measurability of
`f (· + a)` on the open unit cube agree with those of `f`. -/

local instance tMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance tMeasureIsAddHaar2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance tIsProb3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### Cell integrals -/

theorem lintegral_unitCellAt_periodic {f : Vec 2 → ℝ≥0∞} (hf : AVenhance.IsZ2Periodic f)
    (b : Vec 2) : ∫⁻ x in unitCellAt 2 b, f x = ∫⁻ x in unitCell 2, f x := by
  have e := fromUnitTorus_periodicToTorus ((isZdPeriodic_iff_frozen f).2 hf)
  have key : ∀ c : Vec 2,
      ∫⁻ x in unitCellAt 2 c, f x = ∫⁻ y : UnitAddTorus (Fin 2), periodicToTorus f y := by
    intro c
    rw [UnitAddTorus.lintegral_preimage (d := Fin 2) (periodicToTorus f) c]
    change _ = ∫⁻ x in unitCellAt 2 c, fromUnitTorus (periodicToTorus f) x
    rw [e]
  exact (key b).trans (key 0).symm

theorem mem_unitCellAt_add_iff (a x : Vec 2) : x + a ∈ unitCellAt 2 a ↔ x ∈ unitCell 2 := by
  simp only [unitCellAt, unitCell, mem_ofPred_eq, Pi.add_apply, mem_Ioc, zero_add]
  constructor
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]

theorem lintegral_unitCell_translate (f : Vec 2 → ℝ≥0∞) (a : Vec 2) :
    ∫⁻ x in unitCell 2, f (x + a) = ∫⁻ x in unitCellAt 2 a, f x := by
  have h1 := lintegral_indicator (μ := (volume : Measure (Vec 2))) (f := f)
    (measurableSet_unitCellAt 2 a)
  have h2 := lintegral_indicator (μ := (volume : Measure (Vec 2))) (f := fun x => f (x + a))
    (measurableSet_unitCell 2)
  have h3 := lintegral_add_right_eq_self (μ := (volume : Measure (Vec 2)))
    ((unitCellAt 2 a).indicator f) a
  rw [← h1, ← h2, ← h3]
  refine lintegral_congr (fun x => ?_)
  by_cases hx : x ∈ unitCell 2
  · rw [indicator_of_mem hx, indicator_of_mem ((mem_unitCellAt_add_iff a x).2 hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((mem_unitCellAt_add_iff a x).1 h))]

theorem lintegral_cube_translate {f : Vec 2 → ℝ≥0∞} (hf : AVenhance.IsZ2Periodic f) (a : Vec 2) :
    ∫⁻ x in AVenhance.unitCube, f (x + a) = ∫⁻ x in AVenhance.unitCube, f x := by
  have h1 := setLIntegral_congr (μ := (volume : Measure (Vec 2))) (f := fun x => f (x + a))
    unitCell_ae_eq_unitCube
  have h2 := setLIntegral_congr (μ := (volume : Measure (Vec 2))) (f := f)
    unitCell_ae_eq_unitCube
  rw [← h1, ← h2, lintegral_unitCell_translate, lintegral_unitCellAt_periodic hf]

theorem integral_cube_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec 2 → E} (hf : AVenhance.IsZ2Periodic f) (a : Vec 2) :
    ∫ x in AVenhance.unitCube, f (x + a) = ∫ x in AVenhance.unitCube, f x := by
  rw [← integral_unitCell_eq_unitCube, ← integral_unitCell_eq_unitCube]
  have h1 := integral_indicator (μ := (volume : Measure (Vec 2))) (f := f)
    (measurableSet_unitCellAt 2 a)
  have h2 := integral_indicator (μ := (volume : Measure (Vec 2))) (f := fun x => f (x + a))
    (measurableSet_unitCell 2)
  have h3 := integral_add_right_eq_self (μ := (volume : Measure (Vec 2)))
    ((unitCellAt 2 a).indicator f) a
  have h4 : ∫ x in unitCell 2, f (x + a) = ∫ x in unitCellAt 2 a, f x := by
    rw [← h1, ← h2, ← h3]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    by_cases hx : x ∈ unitCell 2
    · simp only [indicator_of_mem hx, indicator_of_mem ((mem_unitCellAt_add_iff a x).2 hx)]
    · simp only [indicator_of_notMem hx,
        indicator_of_notMem (fun h => hx ((mem_unitCellAt_add_iff a x).1 h))]
  rw [h4]
  exact integral_periodic_unitCellAt_eq ((isZdPeriodic_iff_frozen f).2 hf) a

/-! ### A.e. strong measurability -/

theorem cube_closed_ae_eq :
    (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) =ᵐ[(volume : Measure (Vec 2))]
      AVenhance.unitCube := by
  have h₁ :
      (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1) =ᵐ[volume]
        Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := by
    simpa [volume_pi] using
      (Measure.univ_pi_Ioo_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
        (g := fun _ : Fin 2 => (1 : ℝ)))
  exact h₁.symm

/-- The closed unit cube moved by `-n`. -/
def shiftedCube (n : Fin 2 → ℤ) : Set (Vec 2) :=
  (fun x => x + -AVenhance.latticeShift n) ⁻¹' (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem iUnion_shiftedCube : (⋃ n : Fin 2 → ℤ, shiftedCube n) = Set.univ := by
  refine Set.eq_univ_of_forall (fun x => Set.mem_iUnion.2 ⟨fun i => ⌊x i⌋, ?_⟩)
  intro i _
  simp only [Pi.add_apply, Pi.neg_apply, AVenhance.latticeShift]
  constructor
  · linarith [Int.floor_le (x i)]
  · linarith [Int.lt_floor_add_one (x i)]

theorem shiftedCube_mp (n : Fin 2 → ℤ) :
    MeasurePreserving (fun x : Vec 2 => x + -AVenhance.latticeShift n)
      (volume.restrict (shiftedCube n))
      (volume.restrict (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) :=
  (measurePreserving_add_right (volume : Measure (Vec 2)) (-AVenhance.latticeShift n)).restrict_preimage_emb
    (measurableEmbedding_addRight _) _

theorem periodic_sub {β : Type*} {f : Vec 2 → β} (hf : AVenhance.IsZ2Periodic f)
    (n : Fin 2 → ℤ) (x : Vec 2) : f (x + -AVenhance.latticeShift n) = f x := by
  have := hf n (x + -AVenhance.latticeShift n)
  rw [add_assoc, neg_add_cancel, add_zero] at this
  exact this.symm

theorem aestronglyMeasurable_of_cube {β : Type*} [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β] {f : Vec 2 → β}
    (hf : AVenhance.IsZ2Periodic f)
    (h : AEStronglyMeasurable f (volume.restrict AVenhance.unitCube)) :
    AEStronglyMeasurable f (volume : Measure (Vec 2)) := by
  have hK : AEStronglyMeasurable f
      (volume.restrict (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) := by
    rwa [Measure.restrict_congr_set cube_closed_ae_eq]
  have hn : ∀ n : Fin 2 → ℤ, AEStronglyMeasurable f (volume.restrict (shiftedCube n)) := by
    intro n
    have := hK.comp_measurePreserving (shiftedCube_mp n)
    have e : (f ∘ fun x : Vec 2 => x + -AVenhance.latticeShift n) = f :=
      funext (fun x => periodic_sub hf n x)
    rwa [e] at this
  have := (aestronglyMeasurable_iUnion_iff (μ := (volume : Measure (Vec 2)))
    (s := shiftedCube) (f := f)).2 hn
  rwa [iUnion_shiftedCube, Measure.restrict_univ] at this

theorem aestronglyMeasurable_cube_translate {β : Type*} [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β] {f : Vec 2 → β}
    (hf : AVenhance.IsZ2Periodic f)
    (h : AEStronglyMeasurable f (volume.restrict AVenhance.unitCube)) (a : Vec 2) :
    AEStronglyMeasurable (fun x => f (x + a)) (volume.restrict AVenhance.unitCube) :=
  ((aestronglyMeasurable_of_cube hf h).comp_measurePreserving
    (measurePreserving_add_right (volume : Measure (Vec 2)) a)).mono_measure Measure.restrict_le_self

theorem prod_restrict_univ {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (S : Set (Vec 2)) : μ.prod (volume.restrict S) = (μ.prod volume).restrict (Set.univ ×ˢ S) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

theorem aestronglyMeasurable_prod_of_cube {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] {β : Type*} [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β] {F : α × Vec 2 → β}
    (hper : ∀ᵐ t ∂μ, AVenhance.IsZ2Periodic (fun x => F (t, x)))
    (h : AEStronglyMeasurable F (μ.prod (volume.restrict AVenhance.unitCube))) :
    AEStronglyMeasurable F (μ.prod (volume : Measure (Vec 2))) := by
  have hK : AEStronglyMeasurable F
      (μ.prod (volume.restrict (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1))) := by
    rwa [Measure.restrict_congr_set cube_closed_ae_eq]
  have hn : ∀ n : Fin 2 → ℤ, AEStronglyMeasurable F
      ((μ.prod volume).restrict (Set.univ ×ˢ shiftedCube n)) := by
    intro n
    rw [← prod_restrict_univ]
    have mp : MeasurePreserving (Prod.map (id : α → α) fun x : Vec 2 => x + -AVenhance.latticeShift n)
        (μ.prod (volume.restrict (shiftedCube n)))
        (μ.prod (volume.restrict (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1))) :=
      (MeasurePreserving.id μ).prod (shiftedCube_mp n)
    have h1 := hK.comp_measurePreserving mp
    have hae : ∀ᵐ p ∂(μ.prod (volume.restrict (shiftedCube n))),
        AVenhance.IsZ2Periodic (fun x => F (p.1, x)) :=
      Measure.quasiMeasurePreserving_fst.ae hper
    refine h1.congr ?_
    filter_upwards [hae] with p hp
    show F (p.1, p.2 + -AVenhance.latticeShift n) = F (p.1, p.2)
    exact periodic_sub hp n p.2
  have := (aestronglyMeasurable_iUnion_iff (μ := μ.prod (volume : Measure (Vec 2)))
    (s := fun n => Set.univ ×ˢ shiftedCube n) (f := F)).2 hn
  rwa [← Set.prod_iUnion, iUnion_shiftedCube, Set.univ_prod_univ, Measure.restrict_univ] at this

theorem aestronglyMeasurable_prod_cube_translate {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] {β : Type*} [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β] {F : α × Vec 2 → β}
    (hper : ∀ᵐ t ∂μ, AVenhance.IsZ2Periodic (fun x => F (t, x)))
    (h : AEStronglyMeasurable F (μ.prod (volume.restrict AVenhance.unitCube))) (a : Vec 2) :
    AEStronglyMeasurable (fun p : α × Vec 2 => F (p.1, p.2 + a))
      (μ.prod (volume.restrict AVenhance.unitCube)) := by
  have mp : MeasurePreserving (Prod.map (id : α → α) fun x : Vec 2 => x + a)
      (μ.prod (volume : Measure (Vec 2))) (μ.prod (volume : Measure (Vec 2))) :=
    (MeasurePreserving.id μ).prod (measurePreserving_add_right (volume : Measure (Vec 2)) a)
  have h1 := (aestronglyMeasurable_prod_of_cube hper h).comp_measurePreserving mp
  rw [prod_restrict_univ]
  exact h1.mono_measure Measure.restrict_le_self

/-! ### Norms and integrability -/

theorem eLpNorm_cube_translate_of_aesm {β : Type*} [NormedAddCommGroup β] {f : Vec 2 → β}
    (hf : AVenhance.IsZ2Periodic f) (hm : AEStronglyMeasurable f (volume.restrict AVenhance.unitCube))
    (a : Vec 2) :
    eLpNorm (fun x => f (x + a)) 2 (volume.restrict AVenhance.unitCube) =
      eLpNorm f 2 (volume.restrict AVenhance.unitCube) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (aestronglyMeasurable_cube_translate hf hm a),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm]
  have hp : AVenhance.IsZ2Periodic (fun x => ‖f x‖ₑ ^ ((2 : ℝ≥0∞).toReal)) := by
    intro n x
    simp only [hf n x]
  rw [lintegral_cube_translate (f := fun x => ‖f x‖ₑ ^ ((2 : ℝ≥0∞).toReal)) hp a]

theorem isZ2Periodic_translate {β : Type*} {f : Vec 2 → β} (hf : AVenhance.IsZ2Periodic f)
    (a : Vec 2) : AVenhance.IsZ2Periodic (fun x => f (x + a)) := by
  intro n x
  change f (x + AVenhance.latticeShift n + a) = f (x + a)
  rw [add_right_comm]
  exact hf n (x + a)

theorem eLpNorm_cube_translate {β : Type*} [NormedAddCommGroup β] {f : Vec 2 → β}
    (hf : AVenhance.IsZ2Periodic f) (a : Vec 2) :
    eLpNorm (fun x => f (x + a)) 2 (volume.restrict AVenhance.unitCube) =
      eLpNorm f 2 (volume.restrict AVenhance.unitCube) := by
  by_cases hm : AEStronglyMeasurable f (volume.restrict AVenhance.unitCube)
  · exact eLpNorm_cube_translate_of_aesm hf hm a
  · have hm' : ¬ AEStronglyMeasurable (fun x => f (x + a))
        (volume.restrict AVenhance.unitCube) := by
      intro h'
      apply hm
      have := aestronglyMeasurable_cube_translate (isZ2Periodic_translate hf a) h' (-a)
      simpa using this
    rw [eLpNorm_of_not_aestronglyMeasurable hm', eLpNorm_of_not_aestronglyMeasurable hm]

theorem memLp_cube_translate {β : Type*} [NormedAddCommGroup β] {f : Vec 2 → β}
    (hf : AVenhance.IsZ2Periodic f) (h : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (a : Vec 2) : MemLp (fun x => f (x + a)) 2 (volume.restrict AVenhance.unitCube) := by
  rw [memLp_iff, eLpNorm_cube_translate hf a]
  exact h

theorem integrable_cube_translate {β : Type*} [NormedAddCommGroup β] {f : Vec 2 → β}
    (hf : AVenhance.IsZ2Periodic f) (h : Integrable f (volume.restrict AVenhance.unitCube))
    (a : Vec 2) : Integrable (fun x => f (x + a)) (volume.restrict AVenhance.unitCube) := by
  refine ⟨aestronglyMeasurable_cube_translate hf h.1 a, ?_⟩
  have hp : AVenhance.IsZ2Periodic (fun x => ‖f x‖ₑ) := by
    intro n x
    simp only [hf n x]
  have := h.2
  unfold HasFiniteIntegral at this ⊢
  rwa [lintegral_cube_translate (f := fun x => ‖f x‖ₑ) hp a]

theorem ae_zero_cube_translate {β : Type*} [NormedAddCommGroup β] {f : Vec 2 → β}
    (hf : AVenhance.IsZ2Periodic f) (h : f =ᵐ[volume.restrict AVenhance.unitCube] 0) (a : Vec 2) :
    (fun x => f (x + a)) =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  have h0 : AEStronglyMeasurable f (volume.restrict AVenhance.unitCube) :=
    aestronglyMeasurable_zero.congr h.symm
  have h1 : eLpNorm f 2 (volume.restrict AVenhance.unitCube) = 0 :=
    (eLpNorm_eq_zero_iff (by norm_num)).2 h
  have h2 : eLpNorm (fun x => f (x + a)) 2 (volume.restrict AVenhance.unitCube) = 0 := by
    rw [eLpNorm_cube_translate hf a, h1]
  exact (eLpNorm_eq_zero_iff (by norm_num)).1 h2

end AVRegularity.Uniqueness.Translate
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.Uniqueness.Translate

/-! Translation of `CellWeakIdentity`: if the identity holds for a trajectory tested
against the shifted test `ψ'` (with `ψ' (· + a) = ψ`), then the shifted trajectory satisfies it
against `ψ`, provided the coefficients and sources are invariant under `a` and `ℤ²`-periodic and
the integrands are periodic. -/

/-- The right-hand side integrand of `CellWeakIdentity`. -/
def weakRhs (C : CellCoefficients) (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) : ℝ → Vec 2 → ℂ := fun τ x =>
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
        Integrable (weakRhs C ψ dψ u du src F τ) (volume.restrict AVenhance.unitCube)) ∧
      IntegrableOn (fun τ => ∫ x in AVenhance.unitCube, weakRhs C ψ dψ u du src F τ x)
        (Set.Ioc s t) ∧
      (∫ x in AVenhance.unitCube, u₁ x * ψ x) - ∫ x in AVenhance.unitCube, u₀ x * ψ x =
        ∫ τ in Set.Ioc s t, ∫ x in AVenhance.unitCube, weakRhs C ψ dψ u du src F τ x) :=
  Iff.rfl

/-- Pointwise: the right-hand side of the shifted trajectory against `ψ` is the shifted
right-hand side against the shifted test `ψ'`. -/
theorem weakRhs_translate (C : CellCoefficients) (a : Vec 2) (ψ ψ' : Vec 2 → ℂ)
    (dψ dψ' : Fin 2 → Vec 2 → ℂ) (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (τ : ℝ)
    (hψ : ∀ x, ψ' (x + a) = ψ x) (hdψ : ∀ k x, dψ' k (x + a) = dψ k x)
    (hG : ∀ x, C.G τ (x + a) = C.G τ x) (hv : ∀ x, C.v τ (x + a) = C.v τ x)
    (hs : ∀ x, src τ (x + a) = src τ x) (hF : ∀ x, F τ (x + a) = F τ x) (x : Vec 2) :
    weakRhs C ψ dψ (fun τ x => u τ (x + a)) (fun τ k x => du τ k (x + a)) src F τ x =
      weakRhs C ψ' dψ' u du src F τ (x + a) := by
  simp only [weakRhs, hψ, hdψ, hG, hv, hs, hF]

/-- The right-hand side against `ψ'` is `ℤ²`-periodic when all its ingredients are. -/
theorem weakRhs_periodic (C : CellCoefficients) (ψ' : Vec 2 → ℂ) (dψ' : Fin 2 → Vec 2 → ℂ)
    (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (τ : ℝ)
    (hψ : AVenhance.IsZ2Periodic ψ') (hdψ : ∀ k, AVenhance.IsZ2Periodic (dψ' k))
    (hu : AVenhance.IsZ2Periodic (u τ)) (hdu : ∀ k, AVenhance.IsZ2Periodic (du τ k))
    (hG : AVenhance.IsZ2Periodic (C.G τ)) (hv : AVenhance.IsZ2Periodic (C.v τ))
    (hs : AVenhance.IsZ2Periodic (src τ)) (hF : AVenhance.IsZ2Periodic (F τ)) :
    AVenhance.IsZ2Periodic (weakRhs C ψ' dψ' u du src F τ) := by
  intro n x
  simp only [weakRhs, hψ n x, hdψ _ n x, hu n x, hdu _ n x, hG n x, hv n x, hs n x, hF n x]

/-- Translation of the weak identity. -/
theorem cellWeakIdentity_translate (C : CellCoefficients) (s t : ℝ) (a : Vec 2)
    (u₀ u₁ ψ ψ' : Vec 2 → ℂ) (dψ dψ' : Fin 2 → Vec 2 → ℂ) (u : ℝ → Vec 2 → ℂ)
    (du : ℝ → Fin 2 → Vec 2 → ℂ) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hψ : ∀ x, ψ' (x + a) = ψ x) (hdψ : ∀ k x, dψ' k (x + a) = dψ k x)
    (hψp : AVenhance.IsZ2Periodic ψ') (hdψp : ∀ k, AVenhance.IsZ2Periodic (dψ' k))
    (hu₀ : AVenhance.IsZ2Periodic u₀) (hu₁ : AVenhance.IsZ2Periodic u₁)
    (hup : ∀ᵐ τ ∂(volume.restrict (Set.Ioc s t)),
      AVenhance.IsZ2Periodic (u τ) ∧ ∀ k, AVenhance.IsZ2Periodic (du τ k))
    (hGa : ∀ τ ∈ Set.Ioc s t, ∀ x, C.G τ (x + a) = C.G τ x)
    (hGp : ∀ τ ∈ Set.Ioc s t, AVenhance.IsZ2Periodic (C.G τ))
    (hva : ∀ τ ∈ Set.Ioc s t, ∀ x, C.v τ (x + a) = C.v τ x)
    (hvp : ∀ τ ∈ Set.Ioc s t, AVenhance.IsZ2Periodic (C.v τ))
    (hsa : ∀ τ ∈ Set.Ioc s t, ∀ x, src τ (x + a) = src τ x)
    (hsp : ∀ τ ∈ Set.Ioc s t, AVenhance.IsZ2Periodic (src τ))
    (hFa : ∀ τ ∈ Set.Ioc s t, ∀ x, F τ (x + a) = F τ x)
    (hFp : ∀ τ ∈ Set.Ioc s t, AVenhance.IsZ2Periodic (F τ))
    (h : CellWeakIdentity C s t u₀ u₁ ψ' dψ' u du src F) :
    CellWeakIdentity C s t (fun x => u₀ (x + a)) (fun x => u₁ (x + a)) ψ dψ
      (fun τ x => u τ (x + a)) (fun τ k x => du τ k (x + a)) src F := by
  rw [cellWeakIdentity_iff] at h ⊢
  obtain ⟨h1, h0, hI, hO, hE⟩ := h
  have hprod : ∀ w : Vec 2 → ℂ, AVenhance.IsZ2Periodic w →
      AVenhance.IsZ2Periodic (fun x => w x * ψ' x) := by
    intro w hw n x
    simp only [hw n x, hψp n x]
  have e1 : ∫ x in AVenhance.unitCube, u₁ (x + a) * ψ x = ∫ x in AVenhance.unitCube, u₁ x * ψ' x := by
    simpa only [hψ] using integral_cube_translate (hprod u₁ hu₁) a
  have e0 : ∫ x in AVenhance.unitCube, u₀ (x + a) * ψ x = ∫ x in AVenhance.unitCube, u₀ x * ψ' x := by
    simpa only [hψ] using integral_cube_translate (hprod u₀ hu₀) a
  have i1 : Integrable (fun x => u₁ (x + a) * ψ x) (volume.restrict AVenhance.unitCube) := by
    simpa only [hψ] using integrable_cube_translate (hprod u₁ hu₁) h1 a
  have i0 : Integrable (fun x => u₀ (x + a) * ψ x) (volume.restrict AVenhance.unitCube) := by
    simpa only [hψ] using integrable_cube_translate (hprod u₀ hu₀) h0 a
  have hgood : ∀ᵐ τ ∂(volume.restrict (Set.Ioc s t)),
      AVenhance.IsZ2Periodic (weakRhs C ψ' dψ' u du src F τ) ∧
      weakRhs C ψ dψ (fun τ x => u τ (x + a)) (fun τ k x => du τ k (x + a)) src F τ =
        fun x => weakRhs C ψ' dψ' u du src F τ (x + a) := by
    filter_upwards [hup, ae_restrict_mem measurableSet_Ioc] with τ hτ hτm
    refine ⟨weakRhs_periodic C ψ' dψ' u du src F τ hψp hdψp hτ.1 hτ.2 (hGp τ hτm) (hvp τ hτm)
      (hsp τ hτm) (hFp τ hτm), ?_⟩
    funext x
    exact weakRhs_translate C a ψ ψ' dψ dψ' u du src F τ hψ hdψ (hGa τ hτm) (hva τ hτm)
      (hsa τ hτm) (hFa τ hτm) x
  have hint : (fun τ => ∫ x in AVenhance.unitCube, weakRhs C ψ dψ (fun τ x => u τ (x + a))
        (fun τ k x => du τ k (x + a)) src F τ x) =ᵐ[volume.restrict (Set.Ioc s t)]
      fun τ => ∫ x in AVenhance.unitCube, weakRhs C ψ' dψ' u du src F τ x := by
    filter_upwards [hgood] with τ hτ
    rw [hτ.2]
    exact integral_cube_translate hτ.1 a
  refine ⟨i1, i0, ?_, ?_, ?_⟩
  · filter_upwards [hgood, hI] with τ hτ hτI
    rw [hτ.2]
    exact integrable_cube_translate hτ.1 hτI a
  · exact hO.congr hint.symm
  · show (∫ x in AVenhance.unitCube, u₁ (x + a) * ψ x) -
        ∫ x in AVenhance.unitCube, u₀ (x + a) * ψ x = _
    rw [e1, e0, hE]
    exact integral_congr_ae hint.symm

end AVRegularity.Uniqueness.Translate
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.Uniqueness.Translate

/-! Translating a periodic order-`K` weak jet and a torus test function by `a : Vec 2`. -/

theorem hasPeriodicOrderedWeakJet_translate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : ℕ} {D : RawJet2 K E} (h : HasPeriodicOrderedWeakJet D)
    (a : Vec 2) : HasPeriodicOrderedWeakJet (fun b x => D b (x + a)) := by
  obtain ⟨hp, hl, hw⟩ := h
  refine ⟨fun b n x => ?_, fun b => memLp_cube_translate (hp b) (hl b) a,
    CycleJointProofs.orderedWeakJet_translate hw a⟩
  change D b (x + AVenhance.latticeShift n + a) = D b (x + a)
  rw [add_right_comm]
  exact hp b n (x + a)

/-- The translate `ψ (· + a)` of a torus test function. -/
def torusTestTranslate {K : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ψ : TorusHkFunction K E) (a : Vec 2) : TorusHkFunction K E :=
  ⟨fun b x => ψ.jet b (x + a), hasPeriodicOrderedWeakJet_translate ψ.hasPeriodicWeakJet a⟩

theorem torusTestTranslate_jet {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ψ : TorusHkFunction K E) (a : Vec 2) (b : JetIndex2 K) (x : Vec 2) :
    (torusTestTranslate ψ a).jet b x = ψ.jet b (x + a) := rfl

theorem torusTestTranslate_neg_jet {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ψ : TorusHkFunction K E) (a : Vec 2) (b : JetIndex2 K) (x : Vec 2) :
    (torusTestTranslate ψ (-a)).jet b (x + a) = ψ.jet b x := by
  rw [torusTestTranslate_jet, add_assoc, add_neg_cancel, add_zero]

end AVRegularity.Uniqueness.Translate
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.Uniqueness.Translate

/-! Translation of `IsCellSolution` and of its norms: the trajectory
`t ↦ D t (· + a)` is a cell solution for the same data when the coefficients and sources are
invariant under `a` and `ℤ²`-periodic on the interval. -/

/-- The translated trajectory `t ↦ D t (· + a)`. -/
def jetTranslate (D : ℝ → RawJet2 1 ℂ) (a : Vec 2) : ℝ → RawJet2 1 ℂ :=
  fun t b x => D t b (x + a)

theorem cellL2Norm_translate {β : Type*} [NormedAddCommGroup β] {f : Vec 2 → β}
    (hf : AVenhance.IsZ2Periodic f) (a : Vec 2) :
    cellL2Norm (fun x => f (x + a)) = cellL2Norm f :=
  eLpNorm_cube_translate hf a

theorem cellMean_translate {u : Vec 2 → ℂ} (hu : AVenhance.IsZ2Periodic u) (a : Vec 2) :
    cellMean (fun x => u (x + a)) = cellMean u :=
  integral_cube_translate hu a

theorem isZ2Periodic_cellGradient {D : RawJet2 1 ℂ}
    (h : ∀ k, AVenhance.IsZ2Periodic (cellGradComp D k)) :
    AVenhance.IsZ2Periodic (cellGradient D) := by
  intro n x
  change WithLp.toLp 2 (fun k => cellGradComp D k (x + AVenhance.latticeShift n)) =
    WithLp.toLp 2 (fun k => cellGradComp D k x)
  rw [funext (fun k => h k n x)]

/-- Periodicity data of a trajectory: values at every time of `I`, gradient components a.e. -/
theorem cellEnergyNorm_translate (I : Set ℝ) (D : ℝ → RawJet2 1 ℂ) (a : Vec 2)
    (hval : ∀ t ∈ I, AVenhance.IsZ2Periodic (cellValue D t))
    (hgrad : ∀ᵐ t ∂(volume.restrict I), ∀ k, AVenhance.IsZ2Periodic (cellGradComp (D t) k)) :
    cellEnergyNorm I (jetTranslate D a) = cellEnergyNorm I D := by
  unfold cellEnergyNorm cellUlNorm
  have h1 : (⨆ t ∈ I, cellL2Norm (cellValue (jetTranslate D a) t)) =
      ⨆ t ∈ I, cellL2Norm (cellValue D t) := by
    refine iSup_congr (fun t => iSup_congr (fun ht => ?_))
    exact cellL2Norm_translate (hval t ht) a
  have h2 : ∀ r : ℝ, ∫⁻ τ in Icc r (r + 1) ∩ I,
      cellL2Norm (cellGradient (jetTranslate D a τ)) ^ 2 =
      ∫⁻ τ in Icc r (r + 1) ∩ I, cellL2Norm (cellGradient (D τ)) ^ 2 := by
    intro r
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_right hgrad] with τ hτ
    have := cellL2Norm_translate (isZ2Periodic_cellGradient hτ) a
    exact congrArg (· ^ 2) this
  rw [h1]
  congr 2
  funext r
  rw [h2 r]

/-- Translation of the cell solution relation. -/
theorem cellSolution_translate (I : Set ℝ) (C : CellCoefficients) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (D : ℝ → RawJet2 1 ℂ) (a : Vec 2)
    (hGa : ∀ τ ∈ I, ∀ x, C.G τ (x + a) = C.G τ x)
    (hGp : ∀ τ ∈ I, AVenhance.IsZ2Periodic (C.G τ))
    (hva : ∀ τ ∈ I, ∀ x, C.v τ (x + a) = C.v τ x)
    (hvp : ∀ τ ∈ I, AVenhance.IsZ2Periodic (C.v τ))
    (hsa : ∀ τ ∈ I, ∀ x, src τ (x + a) = src τ x)
    (hsp : ∀ τ ∈ I, AVenhance.IsZ2Periodic (src τ))
    (hFa : ∀ τ ∈ I, ∀ x, F τ (x + a) = F τ x)
    (hFp : ∀ τ ∈ I, AVenhance.IsZ2Periodic (F τ))
    (h : IsCellSolution I C src F D) : IsCellSolution I C src F (jetTranslate D a) := by
  obtain ⟨hI, hper, hval, hmeas, hcont, hgrad, hweak⟩ := h
  have hgradp : ∀ᵐ t ∂(volume.restrict I), ∀ k, AVenhance.IsZ2Periodic (cellGradComp (D t) k) := by
    filter_upwards [hper] with t ht k
    exact ht.1 _
  refine ⟨hI, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hper] with t ht
    exact hasPeriodicOrderedWeakJet_translate ht a
  · intro t ht
    exact ⟨memLp_cube_translate (hval t ht).2 (hval t ht).1 a,
      isZ2Periodic_translate (hval t ht).2 a⟩
  · intro b
    have hp : ∀ᵐ t ∂(volume.restrict I), AVenhance.IsZ2Periodic (fun x => D t b x) := by
      filter_upwards [hper] with t ht
      exact ht.1 b
    exact aestronglyMeasurable_prod_cube_translate (F := fun p : ℝ × Vec 2 => D p.1 b p.2) hp
      (hmeas b) a
  · intro t₀ ht₀
    have hh := hcont t₀ ht₀
    refine hh.congr' (eventually_of_mem self_mem_nhdsWithin (fun t ht => ?_))
    have hp : AVenhance.IsZ2Periodic (fun x => ‖cellValue D t x - cellValue D t₀ x‖ₑ ^ 2) := by
      intro n x
      simp only [(hval t ht).2 n x, (hval t₀ ht₀).2 n x]
    exact (lintegral_cube_translate hp a).symm
  · intro r hr s hs
    have hsub : Icc r s ⊆ I := hI.out hr hs
    have := hgrad r hr s hs
    refine lt_of_le_of_lt (le_of_eq ?_) this
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hgradp] with τ hτ
    exact congrArg (· ^ 2) (cellL2Norm_translate (isZ2Periodic_cellGradient hτ) a)
  · intro s hs t ht hst ψ
    have hsub : Ioc s t ⊆ I := fun x hx => hI.out hs ht ⟨hx.1.le, hx.2⟩
    have hw := hweak s hs t ht hst (torusTestTranslate ψ (-a))
    have hψp := (torusTestTranslate ψ (-a)).hasPeriodicWeakJet.1
    refine cellWeakIdentity_translate C s t a (cellValue D s) (cellValue D t)
      (ψ.jet (valueIndex2 1)) ((torusTestTranslate ψ (-a)).jet (valueIndex2 1))
      (fun k => ψ.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
      (fun k => (torusTestTranslate ψ (-a)).jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
      (cellValue D) (fun τ k => cellGradComp (D τ) k) src F
      (fun x => torusTestTranslate_neg_jet ψ a _ x) (fun k x => torusTestTranslate_neg_jet ψ a _ x)
      (hψp _) (fun k => hψp _) (hval s hs).2 (hval t ht).2 ?_
      (fun τ hτ => hGa τ (hsub hτ)) (fun τ hτ => hGp τ (hsub hτ))
      (fun τ hτ => hva τ (hsub hτ)) (fun τ hτ => hvp τ (hsub hτ))
      (fun τ hτ => hsa τ (hsub hτ)) (fun τ hτ => hsp τ (hsub hτ))
      (fun τ hτ => hFa τ (hsub hτ)) (fun τ hτ => hFp τ (hsub hτ)) hw
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hper,
      ae_restrict_mem measurableSet_Ioc] with τ hτ hτm
    exact ⟨(hval τ (hsub hτm)).2, fun k => hτ.1 _⟩

end AVRegularity.Uniqueness.Translate
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter
open AVRegularity.Uniqueness.Translate
namespace AVRegularity.Uniqueness

/-! Translation invariance of the finite-past cell field inverse: the translate
`c t (· + a)` of a cell field inverse of a source and drift invariant under `a` (and
`ℤ²`-periodic, as every cell datum is) is again a cell field inverse of the same source; by
uniqueness on the window the field itself is invariant under `a`. -/

theorem cellJetOfField_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℝ) (c : ℝ → Vec 2 → E) (a : Vec 2) :
    cellJetOfField ℓ (fun t z => c t (z + a)) = jetTranslate (cellJetOfField ℓ c) a := by
  funext t b x
  simp only [cellJetOfField, jetTranslate, fderiv_comp_add_right]

/-- The translate of a cell field inverse is a cell field inverse of the same source. -/
theorem isCellFieldInverse_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {sZ : ℕ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (a : Vec 2)
    (hv : ∀ t z, v t (z + a) = v t z)
    (hvp : ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (v t))
    {g c : ℝ → Vec 2 → E} (hg : ∀ t ∈ Set.Icc t₀ t₁, ∀ z, g t (z + a) = g t z)
    (hgp : ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (g t))
    (hc : IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) g c) :
    IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) g (fun t z => c t (z + a)) := by
  obtain ⟨hsm, hℓ⟩ := hc
  refine ⟨fun t ht => (hsm t ht).comp (contDiff_id.add contDiff_const), fun ℓ => ?_⟩
  obtain ⟨hs, hm, hi, he⟩ := hℓ ℓ
  rw [cellJetOfField_translate]
  have hval : ∀ t ∈ Set.Icc t₀ t₁,
      AVenhance.IsZ2Periodic (cellValue (cellJetOfField ℓ c) t) := fun t ht => (hs.2.2.1 t ht).2
  have hgradp : ∀ᵐ t ∂(volume.restrict (Set.Icc t₀ t₁)),
      ∀ k, AVenhance.IsZ2Periodic (cellGradComp (cellJetOfField ℓ c t) k) := by
    filter_upwards [hs.2.1] with t htp k
    exact htp.1 _
  refine ⟨cellSolution_translate (Set.Icc t₀ t₁) ⟨fun t _ => G t, v, 0, 0⟩ _ (fun _ _ => 0)
    (cellJetOfField ℓ c) a (fun τ _ x => rfl) (fun τ _ n x => rfl)
    (fun τ _ x => hv τ x) hvp
    (fun τ hτ x => by simp only [hg τ hτ x]) (fun τ hτ n x => by simp only [hgp τ hτ n x])
    (fun τ _ x => rfl) (fun τ _ n x => rfl) hs, ?_, ?_, ?_⟩
  · intro t htI
    exact (cellMean_translate (hval t htI) a).trans (hm t htI)
  · have h0 : cellValue (cellJetOfField ℓ c) t₀ =ᵐ[volume.restrict AVenhance.unitCube] 0 :=
      hi.trans (Filter.Eventually.of_forall (fun x => by simp))
    have := ae_zero_cube_translate (hval t₀ ⟨le_rfl, ht⟩) h0 a
    filter_upwards [this] with x hx
    have hx' : cellValue (jetTranslate (cellJetOfField ℓ c) a) t₀ x = 0 := hx
    rw [hx']
    simp
  · rw [cellEnergyNorm_translate _ _ a hval hgradp]
    exact he

/-- A finite-past cell field inverse of a source and drift invariant under the translation `a`
(the drift and the source being `ℤ²`-periodic on the window) is invariant under `a`. -/
theorem cellFieldInverse_translate_invariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {sZ : ℕ} {t₀ t₁ lo A Mv : ℝ} (ht : t₀ ≤ t₁) (hW : WindowData G v t₀ t₁ lo A Mv)
    (a : Vec 2) (hv : ∀ t z, v t (z + a) = v t z)
    (hvp : ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (v t))
    {g c : ℝ → Vec 2 → E} (hg : ∀ t ∈ Set.Icc t₀ t₁, ∀ z, g t (z + a) = g t z)
    (hgp : ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (g t))
    (hc : IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) g c) :
    ∀ t ∈ Set.Icc t₀ t₁, ∀ z, c t (z + a) = c t z := by
  intro t htI z
  exact (cellField_unique_window ht hW (fun t _ z => rfl) hc
    (isCellFieldInverse_translate ht a hv hvp hg hgp hc) t htI z).symm

end AVRegularity.Uniqueness
end
