-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.TorusEnergy.LocalInt
public import Mathlib.MeasureTheory.Function.L2Space
import AVRegularity.Applications.Dissipation.Linear
import AVRegularity.Applications.Dissipation.Positivity

/-! # The fixed-time solution operator on `L²` classes

For a divergence-free window drift and `κ > 0`, the map sending the class of a datum on the cell
to the class of the final slice of its weak solution is a continuous linear operator on
`L²(𝕋²)` (classes on `unitCube`). It is an `L²` contraction, fixes constants, preserves the
mean and is positive (on the window `(a, a + 1)` it is the operator `S` of the proof of
Theorem B of the paper).
An operator whose outputs have continuous periodic representatives has a linear choice of
them. -/

public section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity.Applications.Dissipation

/-- The `L²` norm of a class on the cell is its `l2NormSq`. -/
theorem l2NormSq_coe_eq_norm_sq (f : Lp ℝ 2 (volume.restrict unitCube)) :
    l2NormSq f = ‖f‖ ^ 2 := by
  have hinner := real_inner_self_eq_norm_sq f
  rw [MeasureTheory.L2.inner_def] at hinner
  rw [← hinner]
  unfold l2NormSq
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [pow_two]

/-- Weak solutions with data equal a.e. on the cell have equal slices a.e. on the cell. -/
theorem ae_eq_of_isWeakSolutionOnWith {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} (hκ : 0 < κ)
    (h12 : t₁ < t₂) (hb : IsWindowDrift b t₁ t₂) {f g : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    (hfg : f =ᵐ[volume.restrict unitCube] g) {θ η : ℝ → Vec 2 → ℝ} {Dθ Dη : ℝ → Vec 2 → Vec 2}
    (hθ : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) (hη : IsWeakSolutionOnWith b κ t₁ t₂ g η Dη) :
    ∀ t ∈ Set.Icc t₁ t₂, θ t =ᵐ[volume.restrict unitCube] η t := by
  obtain ⟨hbm, ⟨C, hC⟩, hbp, -⟩ := hb
  obtain ⟨θ₀, -, huniq⟩ := Wellposed.exists_unique_isWeakSolutionOn t₁ t₂ b
    hbm.aestronglyMeasurable ⟨C, hC⟩ hbp κ hκ h12 f hf
  intro t ht
  have h1 := huniq θ ⟨Dθ, hθ⟩ t ht
  have h2 := huniq η ⟨Dη, isWeakSolutionOnWith_congr_datum hfg.symm hη⟩ t ht
  exact h1.trans h2.symm

/-- **The solution operator.** Existence of the weak solution for every `L²` datum, and a
continuous linear `S` on `L²` classes with: the final slice of every weak solution with datum
`f` is `S f`; `‖S‖ ≤ 1`; `S` fixes constants, preserves the cell mean and is positive. -/
theorem exists_weakSolutionOperator {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} (hκ : 0 < κ)
    (h12 : t₁ < t₂) (hb : IsWindowDrift b t₁ t₂) :
    ∃ S : Lp ℝ 2 (volume.restrict unitCube) →L[ℝ] Lp ℝ 2 (volume.restrict unitCube),
      (∀ f : Lp ℝ 2 (volume.restrict unitCube), ∃ θ : ℝ → Vec 2 → ℝ,
        ∃ Dθ : ℝ → Vec 2 → Vec 2, IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) ∧
      (∀ (f : Lp ℝ 2 (volume.restrict unitCube)) (θ : ℝ → Vec 2 → ℝ)
          (Dθ : ℝ → Vec 2 → Vec 2), IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ →
        θ t₂ =ᵐ[volume.restrict unitCube] S f) ∧
      ‖S‖ ≤ 1 ∧
      (∀ (c : ℝ) (f : Lp ℝ 2 (volume.restrict unitCube)),
        (f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] (fun _ => c) →
          (S f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] (fun _ => c)) ∧
      (∀ f : Lp ℝ 2 (volume.restrict unitCube),
        ∫ x in unitCube, S f x = ∫ x in unitCube, f x) ∧
      (∀ f : Lp ℝ 2 (volume.restrict unitCube),
        (∀ᵐ x ∂(volume.restrict unitCube), 0 ≤ f x) →
          ∀ᵐ x ∂(volume.restrict unitCube), 0 ≤ S f x) := by
  have hb' := hb
  obtain ⟨hbm, ⟨C, hC⟩, hbp, -⟩ := hb'
  have hex : ∀ f : Lp ℝ 2 (volume.restrict unitCube), ∃ θ : ℝ → Vec 2 → ℝ,
      ∃ Dθ : ℝ → Vec 2 → Vec 2, IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ := by
    intro f
    obtain ⟨θ, ⟨Dθ, hθ⟩, -⟩ := Wellposed.exists_unique_isWeakSolutionOn t₁ t₂ b
      hbm.aestronglyMeasurable ⟨C, hC⟩ hbp κ hκ h12 f (Lp.memLp f)
    exact ⟨θ, Dθ, hθ⟩
  choose θF DθF hθF using hex
  have hT : t₂ ∈ Set.Icc t₁ t₂ := ⟨h12.le, le_rfl⟩
  have hmem : ∀ f, MemL2On unitCube (θF f t₂) := fun f => ((hθF f).1 t₂ hT).2
  let S₀ : Lp ℝ 2 (volume.restrict unitCube) → Lp ℝ 2 (volume.restrict unitCube) := fun f =>
    (hmem f).toLp (θF f t₂)
  have hS₀ : ∀ f, (S₀ f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] θF f t₂ := fun f =>
    (hmem f).coeFn_toLp
  -- every weak solution's final slice is `S₀ f`
  have hrep : ∀ (f : Lp ℝ 2 (volume.restrict unitCube)) (g : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
      (Dθ : ℝ → Vec 2 → Vec 2), (f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] g →
      IsWeakSolutionOnWith b κ t₁ t₂ g θ Dθ → θ t₂ =ᵐ[volume.restrict unitCube] S₀ f := by
    intro f g θ Dθ hfg hθ
    have h := ae_eq_of_isWeakSolutionOnWith hκ h12 hb (Lp.memLp f) hfg (hθF f) hθ t₂ hT
    exact h.symm.trans (hS₀ f).symm
  let Slin : Lp ℝ 2 (volume.restrict unitCube) →ₗ[ℝ] Lp ℝ 2 (volume.restrict unitCube) :=
    { toFun := S₀
      map_add' := fun f g => by
        refine Lp.ext ?_
        have hsum := isWeakSolutionOnWith_add (Lp.memLp f) (Lp.memLp g) (hθF f) (hθF g)
        have h := hrep (f + g) _ _ _ (Lp.coeFn_add f g) hsum
        filter_upwards [h, Lp.coeFn_add (S₀ f) (S₀ g), hS₀ f, hS₀ g] with x hx hadd hf hg
        rw [hadd, Pi.add_apply, hf, hg, ← hx]
        rfl
      map_smul' := fun c f => by
        refine Lp.ext ?_
        have hsm := isWeakSolutionOnWith_smul c (hθF f)
        have h := hrep (c • f) _ _ _ (Lp.coeFn_smul c f) hsm
        filter_upwards [h, Lp.coeFn_smul c (S₀ f), hS₀ f] with x hx hsmul hf
        rw [RingHom.id_apply, hsmul, Pi.smul_apply, hf, ← hx]
        rfl }
  have hbound : ∀ f, ‖Slin f‖ ≤ 1 * ‖f‖ := by
    intro f
    have hcontr := (l2NormSq_le_of_weakSolutionOnWith hκ.le h12 hb (Lp.memLp f) (hθF f)).1 t₂ hT
    have e1 : l2NormSq (θF f t₂) = ‖Slin f‖ ^ 2 := by
      rw [← l2NormSq_coe_eq_norm_sq]
      unfold l2NormSq
      refine integral_congr_ae ?_
      filter_upwards [hS₀ f] with x hx
      change θF f t₂ x ^ 2 = (S₀ f) x ^ 2
      rw [hx]
    rw [e1, l2NormSq_coe_eq_norm_sq] at hcontr
    rw [one_mul]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hcontr
  let S := Slin.mkContinuous 1 hbound
  have hSapp : ∀ f, S f = S₀ f := fun f => rfl
  refine ⟨S, fun f => ⟨θF f, DθF f, hθF f⟩, fun f θ Dθ hθ => ?_,
    LinearMap.mkContinuous_norm_le _ zero_le_one _, fun c f hfc => ?_, fun f => ?_,
    fun f hf0 => ?_⟩
  · rw [hSapp]
    exact hrep f f θ Dθ (Filter.EventuallyEq.refl _ _) hθ
  · rw [hSapp]
    have h := hrep f _ _ _ hfc (isWeakSolutionOnWith_const b κ t₁ t₂ c)
    exact h.symm
  · rw [hSapp, integral_congr_ae (hS₀ f)]
    exact integral_eq_of_isWeakSolutionOnWith h12 hb (Lp.memLp f) (hθF f) t₂ hT
  · rw [hSapp]
    have h := ae_nonneg_of_isWeakSolutionOnWith hκ.le h12 hb (Lp.memLp f) hf0 (hθF f) t₂ hT
    filter_upwards [h, hS₀ f] with x hx hS
    rw [hS]
    exact hx

/-- Two continuous `ℤ²`-periodic functions that agree a.e. on the cell agree everywhere. -/
theorem eq_of_continuous_periodic_ae_eq {g h : Vec 2 → ℝ} (hg : Continuous g)
    (hh : Continuous h) (hgp : IsZ2Periodic g) (hhp : IsZ2Periodic h)
    (hgh : g =ᵐ[volume.restrict unitCube] h) : g = h := by
  have hopen : IsOpen (unitCube : Set (Vec 2)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have hcube : Set.EqOn g h unitCube :=
    Measure.eqOn_open_of_ae_eq hgh hopen hg.continuousOn hh.continuousOn
  have hclos : Set.EqOn g h (closure unitCube) := hcube.closure hg hh
  funext x
  let n : Fin 2 → ℤ := fun i => ⌊x i⌋
  let y : Vec 2 := fun i => Int.fract (x i)
  have hy : y ∈ closure (unitCube : Set (Vec 2)) := by
    unfold unitCube
    rw [closure_pi_set]
    intro i _
    rw [closure_Ioo zero_ne_one]
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hx : x = y + latticeShift n := by
    funext i
    change x i = Int.fract (x i) + ((⌊x i⌋ : ℤ) : ℝ)
    rw [Int.fract_add_floor]
  rw [hx, hgp n y, hhp n y]
  exact hclos hy

/-- An operator on `L²` classes whose outputs have continuous periodic representatives has a
linear choice of these representatives. -/
theorem exists_continuous_representative_linearMap
    (S : Lp ℝ 2 (volume.restrict unitCube) →L[ℝ] Lp ℝ 2 (volume.restrict unitCube))
    (hS : ∀ f : Lp ℝ 2 (volume.restrict unitCube), ∃ g : Vec 2 → ℝ, Continuous g ∧
      IsZ2Periodic g ∧ g =ᵐ[volume.restrict unitCube] S f) :
    ∃ P : Lp ℝ 2 (volume.restrict unitCube) →ₗ[ℝ] (Vec 2 → ℝ),
      ∀ f : Lp ℝ 2 (volume.restrict unitCube), Continuous (P f) ∧ IsZ2Periodic (P f) ∧
        P f =ᵐ[volume.restrict unitCube] S f := by
  choose g hgc hgp hge using hS
  refine ⟨{ toFun := g, map_add' := fun f₁ f₂ => ?_, map_smul' := fun c f => ?_ },
    fun f => ⟨hgc f, hgp f, hge f⟩⟩
  · refine eq_of_continuous_periodic_ae_eq (hgc _) ((hgc f₁).add (hgc f₂)) (hgp _)
      (fun k x => by simp [hgp f₁ k x, hgp f₂ k x]) ?_
    filter_upwards [hge (f₁ + f₂), hge f₁, hge f₂, Lp.coeFn_add (S f₁) (S f₂)]
      with x h h1 h2 hadd
    rw [h, map_add, hadd, Pi.add_apply, Pi.add_apply, h1, h2]
  · refine eq_of_continuous_periodic_ae_eq (hgc _) ((hgc f).const_smul c) (hgp _)
      (fun k x => by simp [hgp f k x]) ?_
    filter_upwards [hge (c • f), hge f, Lp.coeFn_smul c (S f)] with x h h1 hsm
    rw [h, map_smul, hsm, RingHom.id_apply, Pi.smul_apply, Pi.smul_apply, h1]

end AVRegularity.Applications.Dissipation

end
