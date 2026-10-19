-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeak.PrimitiveShearWindowBound
public import AVRegularity.Sobolev.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
import AVenhance.Infra.Classical.GalerkinGenerator

section
@[expose] public section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.Transverse

/-! Compactness and integrability helpers for the classical-to-weak cell bridge: continuous
functions of `(t, x)` are bounded on `[a,b] × unitCube`, jointly `L²`, and pair integrably with
`L²` jets. -/

theorem unitCube_subset_closed : AVenhance.unitCube ⊆ Set.pi Set.univ (fun _ : Fin 2 => Icc (0 : ℝ) 1) :=
  fun _ hx i hi => Ioo_subset_Icc_self (hx i hi)

theorem unitCube_measure_lt_top : volume AVenhance.unitCube < ⊤ :=
  lt_of_le_of_lt (measure_mono unitCube_subset_closed)
    (isCompact_univ_pi (fun _ : Fin 2 => (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)))).measure_lt_top

theorem measurableSet_unitCube' : MeasurableSet AVenhance.unitCube :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

instance basicFiniteCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using unitCube_measure_lt_top⟩

theorem exists_bound_cube {E : Type*} [NormedAddCommGroup E] {f : ℝ × Vec 2 → E}
    (hf : Continuous f) (a b : ℝ) :
    ∃ M, ∀ t ∈ Icc a b, ∀ x ∈ AVenhance.unitCube, ‖f (t, x)‖ ≤ M := by
  have hK : IsCompact (Icc a b ×ˢ Set.pi Set.univ (fun _ : Fin 2 => Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_univ_pi (fun _ => isCompact_Icc))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨M, fun t ht x hx => hM (t, x) ⟨ht, unitCube_subset_closed hx⟩⟩

theorem integrable_continuous_mul {f : Vec 2 → ℝ} (hf : Continuous f) {ψ : Vec 2 → ℂ}
    (hψ : MemLp ψ 2 (volume.restrict AVenhance.unitCube)) :
    Integrable (fun x => (f x : ℂ) * ψ x) (volume.restrict AVenhance.unitCube) := by
  obtain ⟨M, hM⟩ := exists_bound_cube (f := fun p : ℝ × Vec 2 => f p.2)
    (hf.comp continuous_snd) 0 0
  have h1 : MemLp (fun x => (f x : ℂ)) 2 (volume.restrict AVenhance.unitCube) := by
    refine MemLp.of_bound (Complex.continuous_ofReal.comp hf).aestronglyMeasurable M ?_
    filter_upwards [ae_restrict_mem measurableSet_unitCube'] with x hx
    simpa using hM 0 ⟨le_rfl, le_rfl⟩ x hx
  exact memLp_one_iff_integrable.mp (h1.mul hψ : MemLp _ 1 _)

end AVRegularity.Providers.Transverse
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.Transverse

/-! The spatial part of the classical-to-weak bridge at a fixed time: for a `C²` periodic field `f`,
a constant matrix `Gm`, a continuous drift `V` and source `gg`, integrating the second-order term
by parts against the weak gradient of an `H¹` test gives the weak right-hand side. -/

theorem periodic_fderiv_apply {f : Vec 2 → ℝ} (hp : AVenhance.IsZ2Periodic f) (j : Fin 2) :
    AVenhance.IsZ2Periodic (fun y => fderiv ℝ f y (basisVec j)) :=
  AVenhance.Infra.Classical.GalerkinGenerator.classicalWordDerivative_periodic [j] f hp

theorem contDiff_one_fderiv_apply {f : Vec 2 → ℝ} (hf : ContDiff ℝ 2 f) (j : Fin 2) :
    ContDiff ℝ 1 (fun y => fderiv ℝ f y (basisVec j)) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem continuous_fderiv_apply {f : Vec 2 → ℝ} (hf : ContDiff ℝ 2 f) (j : Fin 2) :
    Continuous (fun y => fderiv ℝ f y (basisVec j)) :=
  (contDiff_one_fderiv_apply hf j).continuous

/-- Weak right-hand side integrand of the cell equation, simplified for `θ = 0`, `κ = 0`, `F = 0`. -/
def weakRhsSimple (Gm : Matrix (Fin 2) (Fin 2) ℝ) (V : Vec 2 → Vec 2) (gg : Vec 2 → ℝ)
    (f : Vec 2 → ℝ) (ψ : TorusHkFunction 1 ℂ) (x : Vec 2) : ℂ :=
  -(∑ j : Fin 2, ∑ k : Fin 2, (Gm j k : ℂ) * (fderiv ℝ f x (basisVec j) : ℝ) *
      ψ.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
    - ∑ k : Fin 2, (V x k : ℂ) * (fderiv ℝ f x (basisVec k) : ℝ) * ψ.jet (valueIndex2 1) x
    + (gg x : ℂ) * ψ.jet (valueIndex2 1) x

/-- The strong right-hand side of the equation. -/
def strongRhs (Gm : Matrix (Fin 2) (Fin 2) ℝ) (V : Vec 2 → Vec 2) (gg : Vec 2 → ℝ)
    (f : Vec 2 → ℝ) (x : Vec 2) : ℝ :=
  ∑ j : Fin 2, ∑ k : Fin 2, Gm j k *
      fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x (basisVec k)
    - ∑ k : Fin 2, V x k * fderiv ℝ f x (basisVec k) + gg x

theorem weakRhsSimple_integrable_and_integral {Gm : Matrix (Fin 2) (Fin 2) ℝ} {V : Vec 2 → Vec 2}
    {gg f : Vec 2 → ℝ} (hV : Continuous V) (hgg : Continuous gg) (hf : ContDiff ℝ 2 f)
    (hp : AVenhance.IsZ2Periodic f) (ψ : TorusHkFunction 1 ℂ) :
    Integrable (weakRhsSimple Gm V gg f ψ) (volume.restrict AVenhance.unitCube) ∧
    ∫ x in AVenhance.unitCube, weakRhsSimple Gm V gg f ψ x =
      ∫ x in AVenhance.unitCube, (strongRhs Gm V gg f x : ℂ) * ψ.jet (valueIndex2 1) x := by
  have hψ0 := ψ.hasPeriodicWeakJet.2.1 (valueIndex2 1)
  have hψk (k : Fin 2) := ψ.hasPeriodicWeakJet.2.1 ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
  have hq (j : Fin 2) := continuous_fderiv_apply hf j
  have hq' (j k : Fin 2) : Continuous
      (fun y => fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) y (basisVec k)) :=
    ((contDiff_one_fderiv_apply hf j).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hVk (k : Fin 2) : Continuous (fun x => V x k) := (continuous_apply k).comp hV
  let T1 : Fin 2 → Fin 2 → Vec 2 → ℂ := fun j k x =>
    (Gm j k : ℂ) * ((fderiv ℝ f x (basisVec j) : ℝ) * ψ.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
  let T2 : Fin 2 → Fin 2 → Vec 2 → ℂ := fun j k x =>
    (Gm j k : ℂ) * (((fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x (basisVec k) : ℝ) : ℂ) *
      ψ.jet (valueIndex2 1) x)
  let T3 : Fin 2 → Vec 2 → ℂ := fun k x =>
    ((V x k * fderiv ℝ f x (basisVec k) : ℝ) : ℂ) * ψ.jet (valueIndex2 1) x
  let T4 : Vec 2 → ℂ := fun x => (gg x : ℂ) * ψ.jet (valueIndex2 1) x
  have i1 (j k) : Integrable (T1 j k) (volume.restrict AVenhance.unitCube) :=
    (integrable_continuous_mul (hq j) (hψk k)).const_mul _
  have i2 (j k) : Integrable (T2 j k) (volume.restrict AVenhance.unitCube) :=
    (integrable_continuous_mul (hq' j k) hψ0).const_mul _
  have i3 (k) : Integrable (T3 k) (volume.restrict AVenhance.unitCube) :=
    integrable_continuous_mul ((hVk k).mul (hq k)) hψ0
  have i4 : Integrable T4 (volume.restrict AVenhance.unitCube) :=
    integrable_continuous_mul hgg hψ0
  have ibp (j k) : ∫ x in AVenhance.unitCube, T2 j k x = -∫ x in AVenhance.unitCube, T1 j k x := by
    have h := AVRegularity.EntryWeakProofs.classical_weak_first_ibp _ (contDiff_one_fderiv_apply hf j)
      (periodic_fderiv_apply hp j) ψ k
    simp only [T1, T2, integral_const_mul]
    rw [h]
    ring
  have e1 : weakRhsSimple Gm V gg f ψ = fun x =>
      (∑ j, ∑ k, -T1 j k x) - ∑ k, T3 k x + T4 x := by
    funext x
    simp only [weakRhsSimple, T1, T3, T4, Finset.sum_neg_distrib, mul_assoc, Complex.ofReal_mul]
  have e2 : (fun x => (strongRhs Gm V gg f x : ℂ) * ψ.jet (valueIndex2 1) x) = fun x =>
      (∑ j, ∑ k, T2 j k x) - ∑ k, T3 k x + T4 x := by
    funext x
    simp only [strongRhs, T2, T3, T4, Finset.sum_mul, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul, sub_mul, add_mul, mul_assoc]
  have hI : Integrable (fun x => (∑ j, ∑ k, -T1 j k x) - ∑ k, T3 k x + T4 x)
      (volume.restrict AVenhance.unitCube) :=
    ((integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (i1 j k).neg).sub
      (integrable_finsetSum _ fun k _ => i3 k)).add i4
  refine ⟨e1 ▸ hI, ?_⟩
  rw [e1, e2]
  have key (T : Fin 2 → Fin 2 → Vec 2 → ℂ)
      (hT : ∀ j k, Integrable (T j k) (volume.restrict AVenhance.unitCube)) :
      ∫ x in AVenhance.unitCube, ((∑ j, ∑ k, T j k x) - ∑ k, T3 k x + T4 x) =
        (∑ j, ∑ k, ∫ x in AVenhance.unitCube, T j k x) -
          (∑ k, ∫ x in AVenhance.unitCube, T3 k x) + ∫ x in AVenhance.unitCube, T4 x := by
    have hA : Integrable (fun x => ∑ j, ∑ k, T j k x) (volume.restrict AVenhance.unitCube) :=
      integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hT j k
    have hB : Integrable (fun x => ∑ k, T3 k x) (volume.restrict AVenhance.unitCube) :=
      integrable_finsetSum _ fun k _ => i3 k
    refine (integral_add (hA.sub hB) i4).trans ?_
    show (∫ x in AVenhance.unitCube, ((∑ j, ∑ k, T j k x) - ∑ k, T3 k x)) +
      ∫ x in AVenhance.unitCube, T4 x = _
    rw [integral_sub hA hB, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hT j k,
      integral_finsetSum _ fun k _ => i3 k]
    have hj (j : Fin 2) : ∫ x in AVenhance.unitCube, ∑ k, T j k x =
        ∑ k, ∫ x in AVenhance.unitCube, T j k x := integral_finsetSum _ fun k _ => hT j k
    simp only [hj]
  refine (key (fun j k x => -T1 j k x) fun j k => (i1 j k).neg).trans ((?_ : _ = _).trans
    (key T2 i2).symm)
  simp only [integral_neg, ibp]

end AVRegularity.Providers.Transverse
end
end
