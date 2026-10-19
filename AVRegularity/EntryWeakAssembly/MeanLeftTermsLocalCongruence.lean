-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.FiniteStagePaths
import AVRegularity.CycleEvolution.CellEnergySpaceRawSmul
import AVRegularity.EntryWeakAssembly.WindowListL2Representative
public import AVRegularity.EntryWeak.NormalizedPulseTransverse
import AVRegularity.EntryWeakAssembly.WindowFieldExtension
public import AVRegularity.EntryWeak.NormalizedLiftAComponentDecomposition

section
section
/-! Uniformly vanishing metric perturbations have vanishing integrated Hilbert flux energy. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularMetricHilbertFlux_integral_tendsto_zero {A : Type*} (l : Filter A)
    {a b : ℝ} (hab : a ≤ b) (M : A → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (C : A → ℝ) (hm : ∀ X j k, Measurable (fun t => M X t j k))
    (hb : ∀ X t j k, |M X t j k| ≤ C X)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 (volume.restrict (Icc a b)))
    (hc : Tendsto C l (𝓝 0)) :
    Tendsto (fun X => ∫ s in a..b, ∑ k,
      ‖molecularMetricHilbertFlux (M X s) (u s) k‖ ^ 2) l (𝓝 0) := by
  have he (X : A) := molecularMetricHilbertFlux_integral_le hab (M X) (C X) (hm X) (hb X) u hu
  have hn (X : A) : 0 ≤ ∫ s in a..b, ∑ k,
      ‖molecularMetricHilbertFlux (M X s) (u s) k‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun s _ => by positivity)
  have hs : Tendsto (fun X => 4 * C X ^ 2 *
      ∫ s in a..b, ∑ j, ‖cellDerivativeCLM j (u s)‖ ^ 2) l (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul] using
      ((hc.pow 2).const_mul 4).mul_const
        (∫ s in a..b, ∑ j, ‖cellDerivativeCLM j (u s)‖ ^ 2)
  exact squeeze_zero hn he hs

end AVRegularity.WeakEntryProofs
end
end

section
/-! Uniformly bounded metrics preserve vanishing integrated gradient energy of varying states. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularMetricHilbertFlux_state_integral_tendsto_zero {A : Type*} (l : Filter A)
    {a b : ℝ} (hab : a ≤ b) (M : A → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (C : ℝ)
    (hm : ∀ X j k, Measurable (fun t => M X t j k))
    (hb : ∀ X t j k, |M X t j k| ≤ C)
    (u : A → ℝ → TorusHk 1 ℂ)
    (hu : ∀ X, MemLp (u X) 2 (volume.restrict (Icc a b)))
    (hd : Tendsto (fun X => ∫ s in a..b, ∑ j, ‖cellDerivativeCLM j (u X s)‖ ^ 2) l (𝓝 0))
    (k : Fin 2) :
    Tendsto (fun X => ∫ s in a..b, ‖molecularMetricHilbertFlux (M X s) (u X s) k‖ ^ 2)
      l (𝓝 0) := by
  have hi (X : A) : (∫ s in a..b, ‖molecularMetricHilbertFlux (M X s) (u X s) k‖ ^ 2) ≤
      4 * C ^ 2 * ∫ s in a..b, ∑ j, ‖cellDerivativeCLM j (u X s)‖ ^ 2 := by
    have hf (j : Fin 2) := cellTime_normSq_intervalIntegrable hab
      (molecularMetricHilbertFlux_memLp _ (M X) C (hm X) (hb X) (u X) (hu X) j)
    have hs : IntervalIntegrable (fun s => ∑ j,
        ‖molecularMetricHilbertFlux (M X s) (u X s) j‖ ^ 2) volume a b := by
      simpa only [Fin.sum_univ_two, Pi.add_apply] using (hf 0).add (hf 1)
    apply (intervalIntegral.integral_mono_on hab (hf k) hs (fun s _ => ?_)).trans
      (molecularMetricHilbertFlux_integral_le hab (M X) C (hm X) (hb X) (u X) (hu X))
    exact Finset.single_le_sum
      (f := fun j : Fin 2 => ‖molecularMetricHilbertFlux (M X s) (u X s) j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have ht : Tendsto (fun X => 4 * C ^ 2 * ∫ s in a..b,
      ∑ j, ‖cellDerivativeCLM j (u X s)‖ ^ 2) l (𝓝 0) := by
    simpa only [mul_zero] using hd.const_mul (4 * C ^ 2)
  exact squeeze_zero (fun X => intervalIntegral.integral_nonneg hab (fun s _ => sq_nonneg _)) hi ht

end AVRegularity.WeakEntryProofs
end
end

section
/-! The actual differentiated ordered-word metric forcing is square integrable. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {I : Type*}

theorem molecularWordHilbertFluxDerivative_memLp {a b : ℝ}
    (G : List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (u : List I → ℝ → TorusHk 1 ℂ) (i : I) (w : List I) (B : List I → ℝ)
    (hm : ∀ p ∈ independentWordForcing w, ∀ j k, Measurable (fun t => G p.1 t j k))
    (hm₁ : ∀ p ∈ independentWordForcing w, ∀ j k, Measurable (fun t => G (i :: p.1) t j k))
    (hb : ∀ p ∈ independentWordForcing w, ∀ t j k, |G p.1 t j k| ≤ B p.1)
    (hb₁ : ∀ p ∈ independentWordForcing w, ∀ t j k, |G (i :: p.1) t j k| ≤ B (i :: p.1))
    (hu : ∀ p ∈ independentWordForcing w, MemLp (u p.2) 2 (volume.restrict (Icc a b)))
    (hu₁ : ∀ p ∈ independentWordForcing w, MemLp (u (i :: p.2)) 2 (volume.restrict (Icc a b)))
    (k : Fin 2) :
    MemLp (fun t => molecularWordHilbertFluxDerivative G u i w t k) 2 (volume.restrict (Icc a b)) := by
  have hp (p : List I × List I) (h : p ∈ independentWordForcing w) :=
    (molecularMetricHilbertFlux_memLp _ (G (i :: p.1)) (B (i :: p.1))
      (hm₁ p h) (hb₁ p h) (u p.2) (hu p h) k).add
      (molecularMetricHilbertFlux_memLp _ (G p.1) (B p.1)
        (hm p h) (hb p h) (u (i :: p.2)) (hu₁ p h) k)
  unfold molecularWordHilbertFluxDerivative
  generalize independentWordForcing w = l at hp ⊢
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil, Pi.zero_apply] using!
      (MemLp.zero (ε := ComplexCellL2) (p := 2) (μ := volume.restrict (Icc a b)))
  | cons p l ih =>
    simpa only [List.map_cons, List.sum_cons, Pi.add_apply] using!
      (hp p List.mem_cons_self).add (ih (fun q hq => hp q (List.mem_cons_of_mem p hq)))

end AVRegularity.WeakEntryProofs
end
end

section
/-! Each divergence-flux component inherits vanishing integrated perturbation energy. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularMetricHilbertFlux_component_integral_tendsto_zero {A : Type*} (l : Filter A)
    {a b : ℝ} (hab : a ≤ b) (M : A → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (C : A → ℝ) (hm : ∀ X j k, Measurable (fun t => M X t j k))
    (hb : ∀ X t j k, |M X t j k| ≤ C X)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 (volume.restrict (Icc a b)))
    (hc : Tendsto C l (𝓝 0)) (k : Fin 2) :
    Tendsto (fun X => ∫ s in a..b,
      ‖molecularMetricHilbertFlux (M X s) (u s) k‖ ^ 2) l (𝓝 0) := by
  have hf (X : A) (j : Fin 2) := cellTime_normSq_intervalIntegrable hab
    (molecularMetricHilbertFlux_memLp _ (M X) (C X) (hm X) (hb X) u hu j)
  have hn (X : A) : 0 ≤ ∫ s in a..b,
      ‖molecularMetricHilbertFlux (M X s) (u s) k‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun s _ => sq_nonneg _)
  have he (X : A) : (∫ s in a..b, ‖molecularMetricHilbertFlux (M X s) (u s) k‖ ^ 2) ≤
      ∫ s in a..b, ∑ j, ‖molecularMetricHilbertFlux (M X s) (u s) j‖ ^ 2 := by
    have hi : IntervalIntegrable (fun s => ∑ j,
        ‖molecularMetricHilbertFlux (M X s) (u s) j‖ ^ 2) volume a b := by
      simpa only [Fin.sum_univ_two, Pi.add_apply] using (hf X 0).add (hf X 1)
    exact intervalIntegral.integral_mono_on hab (hf X k) hi (fun s _ =>
      Finset.single_le_sum (fun j _ => sq_nonneg ‖molecularMetricHilbertFlux (M X s) (u s) j‖) (Finset.mem_univ k))
  exact squeeze_zero hn he
    (molecularMetricHilbertFlux_integral_tendsto_zero l hab M C hm hb u hu hc)

end AVRegularity.WeakEntryProofs
end
end

section
/-! Genuine scalar reserves give good and centered fields for arbitrary smooth coarse data. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι]

theorem scalarLift_goodField (H n : ℕ) (c : LiftCoeff ι (fun _ => ℝ))
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (2 * H) (fun t z Y => c m.val α t Y z v u 1)) (t : ℝ) :
    GoodField H (liftApply n c (fun _ => f) t) := by
  apply liftApply_goodField_of_coefficients H n c f hf t
  · intro m hm α v u
    exact scalarCoefficient_boxSmooth (2 * H) H H m (by omega) c α v u
      (Qc ⟨m, by omega⟩ α v u) t
  · intro X m hm α v u
    exact (scalarCoefficient_goodField (2 * H) m c α v u
      (Qc ⟨m, by omega⟩ α v u) t).2 X

theorem scalarLift_centField (H n : ℕ) (c : LiftCoeff ι (fun _ => ℝ))
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (2 * H) (fun t z Y => c m.val α t Y z v u 1))
    (hmean : ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ t Y v u ξ,
      fieldCellMean (fun z => c m α t Y z v u ξ) = 0) (t : ℝ) :
    CoefField True H (liftApply n c (fun _ => f) t) := by
  have hg := scalarLift_goodField H n c f hf Qc t
  refine ⟨hg, ?_⟩
  intro _ Y
  funext v
  have hm := scalarLiftApply_component_mean_zero (2 * H) n c (fun _ => f) Qc hmean t Y v
  exact (fieldCellMean_pi_apply _ (hg.continuous_slice Y) v).symm.trans hm

end AVRegularity.WeakEntryProofs
end
end

section
/-! Integrated product-rule remainders of the molecular metric flux vanish. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularMetricHilbertFlux_product_residual
    (M M₀ D : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ)
    (u u₀ du : TorusHk 1 ℂ) (k : Fin 2) :
    r • (molecularMetricHilbertFlux M u k - molecularMetricHilbertFlux M₀ u₀ k) -
      (molecularMetricHilbertFlux D u₀ k + molecularMetricHilbertFlux M₀ du k) =
      molecularMetricHilbertFlux (r • (M - M₀) - D) u₀ k +
      molecularMetricHilbertFlux M (r • (u - u₀) - du) k +
      molecularMetricHilbertFlux (M - M₀) du k := by
  simp only [molecularMetricHilbertFlux, Fin.sum_univ_two, Matrix.sub_apply,
    Matrix.smul_apply, map_sub, map_smul, smul_sub, sub_smul, smul_add, smul_smul]
  module

end AVRegularity.WeakEntryProofs
end
end

section
/-! Real scalar multiplication preserves the molecular weak equation with scaled forcing. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularWeak_const_smul {a b : ℝ} (P : MolecularData)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => dataDualDerivative P t (slice t) (S t) (F t))) (c : ℝ) :
    CellWeakHilbertCurve a b (fun t => c • u t) (fun t => c • slice t)
      (fun t => dataDualDerivative P t (c • slice t) (c • S t) (fun j => c • F t j)) := by
  have hh := cellWeakHilbertCurve_const_smul h c
  have he : (fun t => c • dataDualDerivative P t (slice t) (S t) (F t)) =
      fun t => dataDualDerivative P t (c • slice t) (c • S t) (fun j => c • F t j) := by
    funext t
    exact (molecularDual_smul P t c (slice t) (S t) (F t)).symm
  rw [he] at hh
  exact hh

end AVRegularity.WeakEntryProofs
end
end

section
/-! Finite-window molecular energy estimates use only the actual positive coercivity data. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecular_weak_window_energy_bound {a b : ℝ} (hab : a ≤ b) (P : MolecularData)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => dataDualDerivative P t (slice t) (S t) (F t))) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ^ 2 + ∫ s in a..t, (1 / 2) * ∑ j, ‖cellDerivativeCLM j (slice s)‖ ^ 2 ≤
        (‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 4 * ∑ j, ‖F s j‖ ^ 2) *
          Real.exp ((1 + 8 * P.V ^ 2) * (t - a)) := by
  let R := 1 + 8 * P.V ^ 2
  let f := fun s => ‖S s‖ ^ 2 + 4 * ∑ j, ‖F s j‖ ^ 2
  let d := fun s => (1 / 2) * ∑ j, ‖cellDerivativeCLM j (slice s)‖ ^ 2
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hf : IntervalIntegrable f volume a b := by
    have hsum := (cellTime_normSq_intervalIntegrable hab (hF 0)).add
      (cellTime_normSq_intervalIntegrable hab (hF 1))
    simpa only [f, Fin.sum_univ_two, Pi.add_def] using
      (cellTime_normSq_intervalIntegrable hab hS).add (hsum.const_mul 4)
  have hd : IntervalIntegrable d volume a b := by
    have hdj (j : Fin 2) := cellTime_normSq_intervalIntegrable hab
      ((cellDerivativeCLM j).comp_memLp' h.state)
    simpa only [d, Fin.sum_univ_two, Function.comp_def, Pi.add_def] using
      ((hdj 0).add (hdj 1)).const_mul (1 / 2)
  apply h.energy_dissipation_le_gronwall hab R hR f d hf hd
  · exact Filter.Eventually.of_forall (fun s => by dsimp only [f]; positivity)
  · exact Filter.Eventually.of_forall (fun s => by dsimp only [d]; positivity)
  · filter_upwards [h.agrees] with s hs
    rw [dataDualDerivative_pairing, hs]
    simpa only [d, R, f, add_assoc, dataGeneratorForm] using
      molecularGenerator_source_energy_bound P.G P.v P.V P.metric_coercive
        P.drift_measurable P.drift_bounded s (slice s) (S s) (F s)

end AVRegularity.WeakEntryProofs
end
end

section
/-! The canonical real readout agrees exactly with every genuine higher real carrier. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational

theorem cellClassicalLift_eq_real_high (K : ℕ) (w : TorusHk K ℂ)
    (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (hw : torusHkValueCLM w = u)
    (hu : (fun x => ((u x).re : ℂ)) =ᵐ[volume.restrict AVenhance.unitCube] u) :
    cellClassicalLift u = realClassicalLift K (mapTorusHk Complex.reCLM w) := by
  let f := mapTorusHk Complex.reCLM w
  have he : complexifyCellClass (f.val (valueIndex2 K)) = u := by
    apply Lp.ext
    have hf := mapTorusHk_jet_ae Complex.reCLM w (valueIndex2 K)
    have hc := ContinuousLinearMap.coeFn_compLpL (L := Complex.ofRealCLM) (f.val (valueIndex2 K))
    have hv : w.val (valueIndex2 K) = u := hw
    rw [hv] at hf
    filter_upwards [hf, hc, hu] with x hfx hcx hux
    exact hcx.trans ((congrArg Complex.ofReal hfx).trans hux)
  rw [← he]
  exact cellClassicalLift_eq K f

end AVRegularity.WeakEntryProofs
end
end

section
/-! A bounded measurable metric acts on every genuine finite-window raw energy gradient. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set AVRegularity.CycleEvolution

theorem cell_window_metric_flux_memLp {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hm : Measurable (Function.uncurry G)) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t z i j, |G t z i j| ≤ B)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellSolution (Icc a b) C src F D) :
    MemLp (Function.uncurry (cellMetricFlux G D)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  have hg := IsCellSolution.gradient_memLp hab hD
  apply hg.of_le_mul (cellMetricFlux_aestronglyMeasurable (Icc a b) G D hm hD.2.2.2.1)
    (c := 2 * B)
  exact Filter.Eventually.of_forall (fun p =>
    cellMetricFluxVector_norm_le (G p.1 p.2) B hB (hb p.1 p.2) (cellGradient (D p.1) p.2))

end AVRegularity.WeakEntryProofs
end
end

section
/-! Simultaneous metric and lower-state continuity controls the actual product flux. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularMetricHilbertFlux_product_difference_integral_tendsto_zero {A : Type*}
    (l : Filter A) {a b : ℝ} (hab : a ≤ b)
    (M : A → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (M₀ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (C : ℝ) (δ : A → ℝ)
    (hm : ∀ X j k, Measurable (fun t => M X t j k))
    (hm₀ : ∀ j k, Measurable (fun t => M₀ t j k))
    (hb : ∀ X t j k, |M X t j k| ≤ C)
    (hd : ∀ X t j k, |M X t j k - M₀ t j k| ≤ δ X)
    (hδ : Tendsto δ l (𝓝 0))
    (u : A → ℝ → TorusHk 1 ℂ) (u₀ : ℝ → TorusHk 1 ℂ)
    (hu : ∀ X, MemLp (u X) 2 (volume.restrict (Icc a b)))
    (hu₀ : MemLp u₀ 2 (volume.restrict (Icc a b)))
    (hc : Tendsto (fun X => ∫ s in a..b,
      ∑ j, ‖cellDerivativeCLM j (u X s - u₀ s)‖ ^ 2) l (𝓝 0)) (k : Fin 2) :
    Tendsto (fun X => ∫ s in a..b,
      ‖molecularMetricHilbertFlux (M X s) (u X s) k -
        molecularMetricHilbertFlux (M₀ s) (u₀ s) k‖ ^ 2) l (𝓝 0) := by
  let Δ := fun X t => M X t - M₀ t
  have hΔm X j k : Measurable (fun t => Δ X t j k) := (hm X j k).sub (hm₀ j k)
  have hstate X := (hu X).sub hu₀
  have ht1 := molecularMetricHilbertFlux_state_integral_tendsto_zero l hab M C hm hb
    (fun X t => u X t - u₀ t) hstate hc k
  have ht2 := molecularMetricHilbertFlux_component_integral_tendsto_zero l hab Δ δ
    hΔm hd u₀ hu₀ hδ k
  have hm1 X := molecularMetricHilbertFlux_memLp _ (M X) C (hm X) (hb X)
    (fun t => u X t - u₀ t) (hstate X) k
  have hm2 X := molecularMetricHilbertFlux_memLp _ (Δ X) (δ X) (hΔm X) (hd X) u₀ hu₀ k
  have ht := window_normSq_add_integral_tendsto_zero l hab _ _ hm1 hm2 ht1 ht2
  simpa only [molecularMetricHilbertFlux_difference, Δ] using ht

end AVRegularity.WeakEntryProofs
end
end

section
/-! The resolvent difference identity holds for the complete weak Hilbert trajectories. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularWeak_metric_difference (a b : ℝ) (P : MolecularData)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (CG : ℝ)
    (hgm : ∀ i j, Measurable (fun t => G t i j))
    (hgb : ∀ t i j, |G t i j| ≤ CG)
    (hge : ∀ t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j)
    (S S' : ℝ → ComplexCellL2) (F F' : ℝ → Fin 2 → ComplexCellL2)
    (u v : ℝ → ComplexCellL2) (slice other : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => dataDualDerivative
      (molecularMetricReplacement P G CG hgm hgb hge) t (slice t) (S t) (F t)))
    (h' : CellWeakHilbertCurve a b v other
      (fun t => dataDualDerivative P t (other t) (S' t) (F' t))) :
    CellWeakHilbertCurve a b (fun t => u t - v t) (fun t => slice t - other t)
      (fun t => dataDualDerivative (molecularMetricReplacement P G CG hgm hgb hge) t
        (slice t - other t) (S t - S' t)
        (fun k => F t k - F' t k + molecularMetricHilbertFlux (G t - P.G t) (other t) k)) := by
  have hh := h.sub h'
  have he : (fun t => dataDualDerivative (molecularMetricReplacement P G CG hgm hgb hge) t
      (slice t) (S t) (F t) - dataDualDerivative P t (other t) (S' t) (F' t)) =
      fun t => dataDualDerivative (molecularMetricReplacement P G CG hgm hgb hge) t
        (slice t - other t) (S t - S' t)
        (fun k => F t k - F' t k + molecularMetricHilbertFlux (G t - P.G t) (other t) k) := by
    funext t
    exact molecularDual_metric_difference P G CG hgm hgb hge t (slice t) (other t)
      (S t) (S' t) (F t) (F' t)
  rw [he] at hh
  exact hh

end AVRegularity.WeakEntryProofs
end
end

section
/-! Vanishing forcing budgets also control the integrated gradient of the actual weak solution. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecular_weak_window_gradient_tendsto_zero {A : Type*} (l : Filter A)
    {a b : ℝ} (hab : a ≤ b) (P : A → MolecularData) (V : ℝ)
    (hV : ∀ X, (P X).V = V)
    (S : A → ℝ → ComplexCellL2) (F : A → ℝ → Fin 2 → ComplexCellL2)
    (hS : ∀ X, MemLp (S X) 2 (volume.restrict (Icc a b)))
    (hF : ∀ X j, MemLp (fun t => F X t j) 2 (volume.restrict (Icc a b)))
    (u : A → ℝ → ComplexCellL2) (slice : A → ℝ → TorusHk 1 ℂ)
    (h : ∀ X, CellWeakHilbertCurve a b (u X) (slice X)
      (fun t => dataDualDerivative (P X) t (slice X t) (S X t) (F X t)))
    (B : A → ℝ)
    (hb : ∀ X, ‖u X a‖ ^ 2 + ∫ s in a..b,
      ‖S X s‖ ^ 2 + 4 * ∑ j, ‖F X s j‖ ^ 2 ≤ B X)
    (hsmall : Tendsto B l (𝓝 0)) :
    Tendsto (fun X => ∫ s in a..b, ∑ j, ‖cellDerivativeCLM j (slice X s)‖ ^ 2)
      l (𝓝 0) := by
  let I := fun X => ∫ s in a..b, ∑ j, ‖cellDerivativeCLM j (slice X s)‖ ^ 2
  let E := Real.exp ((1 + 8 * V ^ 2) * (b - a))
  have he (X : A) : (1 / 2) * I X ≤ B X * E := by
    have hh := molecular_weak_window_energy_bound hab (P X) (S X) (F X)
      (hS X) (hF X) (u X) (slice X) (h X) b ⟨hab, le_rfl⟩
    rw [intervalIntegral.integral_const_mul, hV X] at hh
    exact (le_add_of_nonneg_left (sq_nonneg _)).trans
      (hh.trans (mul_le_mul_of_nonneg_right (hb X) (Real.exp_nonneg _)))
  have hi (X : A) : I X ≤ 2 * (B X * E) := calc
    I X = 2 * ((1 / 2) * I X) := by ring
    _ ≤ 2 * (B X * E) := mul_le_mul_of_nonneg_left (he X) (by norm_num)
  have ht : Tendsto (fun X => 2 * (B X * E)) l (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using (hsmall.mul_const E).const_mul 2
  exact squeeze_zero (fun X => intervalIntegral.integral_nonneg hab
    (fun s _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))) hi ht

end AVRegularity.WeakEntryProofs
end
end

section
/-! A common forcing energy budget bounds the complete finite-window trajectory. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecular_weak_window_value_bound {a b : ℝ} (hab : a ≤ b) (P : MolecularData)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => dataDualDerivative P t (slice t) (S t) (F t)))
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 4 * ∑ j, ‖F s j‖ ^ 2 ≤ B) :
    ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ B * Real.exp ((1 + 8 * P.V ^ 2) * (b - a)) := by
  intro t ht
  have he := molecular_weak_window_energy_bound hab P S F hS hF u slice h t ht
  have hi : 0 ≤ ∫ s in a..t, (1 / 2 : ℝ) * ∑ j, ‖cellDerivativeCLM j (slice s)‖ ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 (fun s _ => by positivity)
  have hv : ‖u t‖ ^ 2 ≤ (‖u a‖ ^ 2 + ∫ s in a..b,
      ‖S s‖ ^ 2 + 4 * ∑ j, ‖F s j‖ ^ 2) *
      Real.exp ((1 + 8 * P.V ^ 2) * (t - a)) := le_trans (le_add_of_nonneg_right hi) he
  apply hv.trans
  exact mul_le_mul hb
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) (by positivity)))
    (Real.exp_nonneg _) hB

end AVRegularity.WeakEntryProofs
end
end

section
/-! Vanishing finite-window forcing budgets imply convergence of the actual energy traces. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecular_weak_window_value_tendsto_zero {A : Type*} (l : Filter A)
    {a b : ℝ} (hab : a ≤ b) (P : A → MolecularData) (V : ℝ)
    (hV : ∀ X, (P X).V = V)
    (S : A → ℝ → ComplexCellL2) (F : A → ℝ → Fin 2 → ComplexCellL2)
    (hS : ∀ X, MemLp (S X) 2 (volume.restrict (Icc a b)))
    (hF : ∀ X j, MemLp (fun t => F X t j) 2 (volume.restrict (Icc a b)))
    (u : A → ℝ → ComplexCellL2) (slice : A → ℝ → TorusHk 1 ℂ)
    (h : ∀ X, CellWeakHilbertCurve a b (u X) (slice X)
      (fun t => dataDualDerivative (P X) t (slice X t) (S X t) (F X t)))
    (B : A → ℝ) (hB : ∀ X, 0 ≤ B X)
    (hb : ∀ X, ‖u X a‖ ^ 2 + ∫ s in a..b,
      ‖S X s‖ ^ 2 + 4 * ∑ j, ‖F X s j‖ ^ 2 ≤ B X)
    (hsmall : Tendsto B l (𝓝 0)) (t : ℝ) (ht : t ∈ Icc a b) :
    Tendsto (fun X => u X t) l (𝓝 0) := by
  have he (X : A) : ‖u X t‖ ^ 2 ≤ B X * Real.exp ((1 + 8 * V ^ 2) * (b - a)) := by
    simpa only [hV X] using
      molecular_weak_window_value_bound hab (P X) (S X) (F X) (hS X) (hF X)
        (u X) (slice X) (h X) (B X) (hB X) (hb X) t ht
  have hn (X : A) : ‖u X t‖ ≤ Real.sqrt (B X * Real.exp ((1 + 8 * V ^ 2) * (b - a))) :=
    (Real.le_sqrt (norm_nonneg _) (mul_nonneg (hB X) (Real.exp_nonneg _))).2 (he X)
  have hs : Tendsto (fun X => Real.sqrt (B X * Real.exp ((1 + 8 * V ^ 2) * (b - a))))
      l (𝓝 0) := by
    simpa only [zero_mul, Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto (0 * Real.exp ((1 + 8 * V ^ 2) * (b - a)))).comp
        (hsmall.mul_const (Real.exp ((1 + 8 * V ^ 2) * (b - a))))
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun X => norm_nonneg (u X t)) hn hs)

end AVRegularity.WeakEntryProofs
end
end

section
/-! A metric difference quotient minus its differentiated solution has an explicit residual forcing. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularWeak_metric_quotient_error (a b : ℝ) (P : MolecularData)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (CG : ℝ)
    (hm : ∀ i j, Measurable (fun t => G t i j))
    (hb : ∀ t i j, |G t i j| ≤ CG)
    (he : ∀ t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j)
    (c : ℝ) (S S' S₁ : ℝ → ComplexCellL2) (F F' F₁ : ℝ → Fin 2 → ComplexCellL2)
    (u v w : ℝ → ComplexCellL2) (slice other deriv : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => dataDualDerivative
      (molecularMetricReplacement P G CG hm hb he) t (slice t) (S t) (F t)))
    (h' : CellWeakHilbertCurve a b v other
      (fun t => dataDualDerivative P t (other t) (S' t) (F' t)))
    (h₁ : CellWeakHilbertCurve a b w deriv
      (fun t => dataDualDerivative P t (deriv t) (S₁ t) (F₁ t))) :
    CellWeakHilbertCurve a b (fun t => c • (u t - v t) - w t)
      (fun t => c • (slice t - other t) - deriv t)
      (fun t => dataDualDerivative (molecularMetricReplacement P G CG hm hb he) t
        (c • (slice t - other t) - deriv t) (c • (S t - S' t) - S₁ t)
        (fun j => c • (F t j - F' t j + molecularMetricHilbertFlux (G t - P.G t) (other t) j) -
          F₁ t j + molecularMetricHilbertFlux (G t - P.G t) (deriv t) j)) := by
  have hd := molecularWeak_metric_difference a b P G CG hm hb he
    S S' F F' u v slice other h h'
  have hq := molecularWeak_const_smul (molecularMetricReplacement P G CG hm hb he)
    (fun t => S t - S' t)
    (fun t j => F t j - F' t j + molecularMetricHilbertFlux (G t - P.G t) (other t) j)
    (fun t => u t - v t) (fun t => slice t - other t) hd c
  exact molecularWeak_metric_difference a b P G CG hm hb he
    (fun t => c • (S t - S' t)) S₁
    (fun t j => c • (F t j - F' t j + molecularMetricHilbertFlux (G t - P.G t) (other t) j)) F₁
    (fun t => c • (u t - v t)) w (fun t => c • (slice t - other t)) deriv hq h₁

end AVRegularity.WeakEntryProofs
end
end
end

section
section
/-! Lower-word gradient continuity produces continuity of the literal ordered-word forcing. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {A I : Type*}

theorem molecularWordHilbertFlux_difference_integral_tendsto_zero
    (l : Filter A) {a b : ℝ} (hab : a ≤ b)
    (G : List I → A → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (G₀ : List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (u : List I → A → ℝ → TorusHk 1 ℂ) (u₀ : List I → ℝ → TorusHk 1 ℂ)
    (w : List I) (C : List I → ℝ) (δ : List I → A → ℝ)
    (hm : ∀ p ∈ independentWordForcing w, ∀ X j k, Measurable (fun t => G p.1 X t j k))
    (hm₀ : ∀ p ∈ independentWordForcing w, ∀ j k, Measurable (fun t => G₀ p.1 t j k))
    (hb : ∀ p ∈ independentWordForcing w, ∀ X t j k, |G p.1 X t j k| ≤ C p.1)
    (hd : ∀ p ∈ independentWordForcing w, ∀ X t j k,
      |G p.1 X t j k - G₀ p.1 t j k| ≤ δ p.1 X)
    (hδ : ∀ p ∈ independentWordForcing w, Tendsto (δ p.1) l (𝓝 0))
    (hu : ∀ p ∈ independentWordForcing w, ∀ X, MemLp (u p.2 X) 2 (volume.restrict (Icc a b)))
    (hu₀ : ∀ p ∈ independentWordForcing w, MemLp (u₀ p.2) 2 (volume.restrict (Icc a b)))
    (hc : ∀ p ∈ independentWordForcing w, Tendsto (fun X => ∫ s in a..b,
      ∑ j, ‖cellDerivativeCLM j (u p.2 X s - u₀ p.2 s)‖ ^ 2) l (𝓝 0))
    (k : Fin 2) :
    Tendsto (fun X => ∫ s in a..b,
      ‖molecularWordHilbertFlux (fun p => G p X) (fun p => u p X) w s k -
        molecularWordHilbertFlux G₀ u₀ w s k‖ ^ 2) l (𝓝 0) := by
  have hmem (p : List I × List I) (hp : p ∈ independentWordForcing w) (X : A) :
      MemLp (fun t => molecularMetricHilbertFlux (G p.1 X t) (u p.2 X t) k -
        molecularMetricHilbertFlux (G₀ p.1 t) (u₀ p.2 t) k) 2 (volume.restrict (Icc a b)) := by
    let Δ := fun t => G p.1 X t - G₀ p.1 t
    have hΔm j k : Measurable (fun t => Δ t j k) :=
      (hm p hp X j k).sub (hm₀ p hp j k)
    have hh := (molecularMetricHilbertFlux_memLp _ (G p.1 X) (C p.1) (hm p hp X)
      (hb p hp X) (fun t => u p.2 X t - u₀ p.2 t) ((hu p hp X).sub (hu₀ p hp)) k).add
      (molecularMetricHilbertFlux_memLp _ Δ (δ p.1 X) hΔm (hd p hp X)
        (u₀ p.2) (hu₀ p hp) k)
    simpa only [molecularMetricHilbertFlux_difference, Δ, Pi.add_apply] using! hh
  have ht := window_normSq_list_sum_integral_tendsto_zero l hab (independentWordForcing w)
    (fun p X t => molecularMetricHilbertFlux (G p.1 X t) (u p.2 X t) k -
      molecularMetricHilbertFlux (G₀ p.1 t) (u₀ p.2 t) k) hmem
    (fun p hp => molecularMetricHilbertFlux_product_difference_integral_tendsto_zero l hab
      (G p.1) (G₀ p.1) (C p.1) (δ p.1) (hm p hp) (hm₀ p hp) (hb p hp) (hd p hp)
      (hδ p hp) (u p.2) (u₀ p.2) (hu p hp) (hu₀ p hp) (hc p hp) k)
  simpa only [molecularWordHilbertFlux, window_list_sum_apply, List.map_map,
    Function.comp_def, window_list_sum_sub] using ht

end AVRegularity.WeakEntryProofs
end
end

section
/-! The strictly lower ordered-word metric forcing is square integrable on the actual window. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution
variable {I : Type*}

theorem word_metric_flux_window_memLp {a b : ℝ} (hab : a ≤ b)
    (G : List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (c : List I → ℝ → RawJet2 1 ℂ) (w : List I)
    (B : List I → ℝ)
    (hB : ∀ p ∈ independentWordForcing w, 0 ≤ B p.1)
    (hm : ∀ p ∈ independentWordForcing w, ∀ i j, Measurable (fun t => G p.1 t i j))
    (hb : ∀ p ∈ independentWordForcing w, ∀ t i j, |G p.1 t i j| ≤ B p.1)
    (C : CellCoefficients) (src : List I → ℝ → Vec 2 → ℂ)
    (F : List I → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hc : ∀ p ∈ independentWordForcing w,
      IsCellSolution (Icc a b) C (src p.2) (F p.2) (c p.2)) :
    MemLp (Function.uncurry (independentWordMetricFlux (fun p t _ => G p t) c w)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  have hp (p : List I × List I) (h : p ∈ independentWordForcing w) :
      MemLp (Function.uncurry (cellMetricFlux (fun t (_ : Vec 2) => G p.1 t) (c p.2))) 2
        ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) :=
    cell_window_metric_flux_memLp hab _
      (Measurable.of_eval (fun i => Measurable.of_eval (fun j => (hm p h i j).comp measurable_fst)))
      (B p.1) (hB p h) (fun t _ => hb p h t) (hc p h)
  unfold independentWordMetricFlux
  generalize independentWordForcing w = l at hp ⊢
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using! (MemLp.zero (p := (2 : ENNReal))
      (μ := (volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))
      (ε := PiLp 2 (fun _ : Fin 2 => ℂ)))
  | cons p l ih =>
    have ht := ih (fun q hq => hp q (List.mem_cons_of_mem p hq))
    simpa only [List.map_cons, List.sum_cons] using! (hp p (List.mem_cons_self)).add ht

end AVRegularity.WeakEntryProofs
end
end
end

section
section
/-! The successor's independent fields are the actual weak mean, chain-rule transfer and carrier pin. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

open Homogenization AVRegularity.Sobolev
open scoped Classical

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

def weakSourceTransferredFlux (G : GenStage D ScalarH Dm b j₀) (η : ℝ)
    (Cc : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (p : OddSlot) (c : StageCtx D b j₀ (G.level - 1) p) (s : WeakSource G)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2) : Vec 2 :=
  if IsAdmissibleChain D b j₀ (G.level - 1) p.1
      (c.1.recenter D (D.eps (G.level - 1 - 1) • X)) then
    transferAt D G.level p.1 (s.lam G.level η) s.degree
      (s.fluxOp (D.eps (G.level - 1)) (Cc s) Cc0) t
      (c.1.recenter D (D.eps (G.level - 1 - 1) • X)) z d I
  else 0

end AVRegularity.WeakEntryProofs
end
end

section
/-! The actual weak transfer vanishes above its original source degree. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

open Homogenization AVRegularity.Sobolev

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem transferAt_above_degree (D : OCData) (m : ℕ) (p : ℤ) (lam : ℝ)
    (degree : ℕ) (fop : FamFluxOp) (t : ℝ) (A : RealChain) (z : Vec 2)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (hd : degree < d) :
    transferAt D m p lam degree fop t A z d I = 0 := by
  unfold transferAt
  have hz : ∀ k : ℤ,
      transportedCoeff
        (fun h => (childTransition D k t (A.recenter D h) (z + (D.eps (m - 1))⁻¹ • h))⁻¹)
        degree (fun d I => fluxCoeff (fop k t (A.appendChild D k t z)) d I 0)
        (d - 1) I 0 = 0 := by
    intro k
    exact CycleJointProofs.transportedCoeff_zero_at_or_above _ _ _ _ (by omega) _ _
  simp only [hz, smul_zero, finsum_zero]

theorem weakSourceTransferredFlux_above_degree (G : GenStage D ScalarH Dm b j₀) (η : ℝ)
    (Cc : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (p : OddSlot) (c : StageCtx D b j₀ (G.level - 1) p) (s : WeakSource G)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2) (hd : s.degree < d) :
    weakSourceTransferredFlux G η Cc Cc0 p c s d I t X z = 0 := by
  unfold weakSourceTransferredFlux
  split
  · exact transferAt_above_degree _ _ _ _ _ _ _ _ _ _ _ hd
  · rfl

end AVRegularity.WeakEntryProofs
end
end

section
/-! Literal inherited Taylor terms retain genuine reserves without matrix price assumptions. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def inheritedTaylorReserve (H : ℕ) (hD : 1 ≤ D)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (A : Vec 2 →L[ℝ] ℝ)
    (hh n : ℕ) (u v : ι) (k : Fin 2) (j : ℕ)
    (Qf : ∀ w, JointSourceReserve (H + D)
      (fun t z Y => normalizedLiftTestField (Cc (hh - 1) (n - j)) (n - j) A u w 1 t Y z))
    (Qedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      JointSourceReserve H (fun t z Y => γ.coeff α t Y z)) :
    JointSourceReserve H (normalizedLiftInheritedTaylor Q Cc A hh n u v k j) := by
  let f := fun t z Y w => normalizedLiftTestField (Cc (hh - 1) (n - j)) (n - j) A u w 1 t Y z
  let Qwhole := jointSourcePiReserve (H + D) (fun w t z Y => f t z Y w) Qf
  let R := normalizedSourceFluxReserve H Q.edge Q.η A f Qwhole Qedge k (j - 1) v
  apply R.congrSource
  funext t z Y
  have hg := Qwhole.exponentialGoodField A t
  have he : (fun X y => Real.exp (A X) • f t y X) =
      liftApply (n - j) (Cc (hh - 1) (n - j))
        (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) t := by
    exact normalizedLiftTestField_exp_cancel _ _ _ _ t
  dsimp only [normalizedLiftInheritedTaylor]
  rw [← he]
  rw [sourceFluxCoefficientArray_normalized Q.edge hD Q.η t _
    (hg.mono (by omega)) k (j - 1) Y z]

end AVRegularity.WeakEntryProofs
end
end
end

section
section
/-! Vanishing differentiated-equation residuals identify the actual finite-window trace derivative. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularWeak_metric_quotient_gradient_tendsto {A : Type*} (l : Filter A)
    {a b : ℝ} (hab : a ≤ b) (P : MolecularData)
    (G : A → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (CG : A → ℝ)
    (hm : ∀ X i j, Measurable (fun t => G X t i j))
    (hb : ∀ X t i j, |G X t i j| ≤ CG X)
    (he : ∀ X t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G X t i j * ξ i * ξ j)
    (c : A → ℝ) (D : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (S : A → ℝ → ComplexCellL2) (S₀ S₁ : ℝ → ComplexCellL2)
    (F : A → ℝ → Fin 2 → ComplexCellL2) (F₀ F₁ : ℝ → Fin 2 → ComplexCellL2)
    (u : A → ℝ → ComplexCellL2) (v w : ℝ → ComplexCellL2)
    (slice : A → ℝ → TorusHk 1 ℂ) (other deriv : ℝ → TorusHk 1 ℂ)
    (h : ∀ X, CellWeakHilbertCurve a b (u X) (slice X) (fun t => dataDualDerivative
      (molecularMetricReplacement P (G X) (CG X) (hm X) (hb X) (he X)) t
        (slice X t) (S X t) (F X t)))
    (h₀ : CellWeakHilbertCurve a b v other
      (fun t => dataDualDerivative P t (other t) (S₀ t) (F₀ t)))
    (h₁ : CellWeakHilbertCurve a b w deriv (fun t => dataDualDerivative P t (deriv t)
      (S₁ t) (fun j => F₁ t j + molecularMetricHilbertFlux (D t) (other t) j)))
    (hS : ∀ X, MemLp (fun t => c X • (S X t - S₀ t) - S₁ t) 2
      (volume.restrict (Icc a b)))
    (hF : ∀ X j, MemLp (fun t => (c X • (F X t j - F₀ t j) - F₁ t j) +
      molecularMetricHilbertFlux (c X • (G X t - P.G t) - D t) (other t) j +
      molecularMetricHilbertFlux (G X t - P.G t) (deriv t) j) 2
        (volume.restrict (Icc a b)))
    (B : A → ℝ)
    (hbudget : ∀ X, ‖c X • (u X a - v a) - w a‖ ^ 2 + ∫ t in a..b,
      ‖c X • (S X t - S₀ t) - S₁ t‖ ^ 2 + 4 * ∑ j,
      ‖(c X • (F X t j - F₀ t j) - F₁ t j) +
        molecularMetricHilbertFlux (c X • (G X t - P.G t) - D t) (other t) j +
        molecularMetricHilbertFlux (G X t - P.G t) (deriv t) j‖ ^ 2 ≤ B X)
    (hsmall : Tendsto B l (𝓝 0)) :
    Tendsto (fun X => ∫ t in a..b, ∑ j,
      ‖cellDerivativeCLM j (c X • (slice X t - other t) - deriv t)‖ ^ 2) l (𝓝 0) := by
  let Q := fun X => molecularMetricReplacement P (G X) (CG X) (hm X) (hb X) (he X)
  have hd (X : A) := molecularWeak_metric_quotient_error a b P (G X) (CG X)
    (hm X) (hb X) (he X) (c X) (S X) S₀ S₁ (F X) F₀
    (fun t j => F₁ t j + molecularMetricHilbertFlux (D t) (other t) j)
    (u X) v w (slice X) other deriv (h X) h₀ h₁
  simp_rw [molecularMetricHilbertFlux_quotient_residual] at hd
  exact molecular_weak_window_gradient_tendsto_zero l hab Q P.V (fun _ => rfl)
    (fun X t => c X • (S X t - S₀ t) - S₁ t)
    (fun X t j => (c X • (F X t j - F₀ t j) - F₁ t j) +
      molecularMetricHilbertFlux (c X • (G X t - P.G t) - D t) (other t) j +
      molecularMetricHilbertFlux (G X t - P.G t) (deriv t) j)
    hS hF (fun X t => c X • (u X t - v t) - w t)
    (fun X t => c X • (slice X t - other t) - deriv t) hd B hbudget hsmall

end AVRegularity.WeakEntryProofs
end
end

section
/-! The diagonal mean formulas require regular metric and drift fields, with no transverse setting. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] {D : ℕ}

theorem weakDiagonal_mean_flux_coefficient_vector_apply
    (Q : LiftOperatorData ι h D) (t : ℝ)
    (hv : ∀ k, Continuous (fun y => Real.sqrt Q.η * Q.v t y k))
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (n : ℕ) (hn : 2 ≤ n) (f : Vec 2 → ∀ i, h i)
    (k₀ : Fin 2) (X z : Vec 2)
    (hc : ∀ m ≤ n - 1, ∀ α : DerivativeWord2 m, ∀ v u,
      Continuous (fun y => Cc 0 (n - 1) m α t X y v u)) :
    liftApply (n - 1) (diagonalMeanFluxCoefficient Q Cc n k₀) (fun _ => f) t X z =
      fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k₀) •
        liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t X y) +
      if n = 2 then -Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fderiv ℝ f X (basisVec j) else 0 := by
  let c := weightedLiftCoefficientMean (Cc 0 (n - 1))
    (fun t z => Real.sqrt Q.η * Q.v t z k₀)
  have hw : Continuous (fun y => Real.sqrt Q.η * Q.v t y k₀) :=
    hv k₀
  have hfast : Continuous (liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t X) :=
    continuous_pi (fun v => liftApply_component_fast_continuous (n - 1) _ _ t X v
      (fun m hm α u => hc m hm α v u))
  have hca : liftApply (n - 1) c (fun _ => f) t X z =
      fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k₀) •
        liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t X y) := by
    ext v
    rw [weightedLiftCoefficientMean_apply (n - 1) _ _ _ t X z v hw (fun m hm α u => hc m hm α v u)]
    exact fieldCellMean_pi_apply _ (hw.smul hfast) v
  change liftApply (n - 1) (fun m α t X z v u => c m α t X z v u +
    if n = 2 then metricFluxCoefficient Q.η Q.G k₀ m α t X z v u else 0) (fun _ => f) t X z = _
  by_cases hn2 : n = 2
  · subst n
    simp only [ite_true]
    rw [liftApply_coefficient_add]
    dsimp only
    rw [metricFluxCoefficient_apply, hca]
  · simp only [ite_eq_right hn2, add_zero, hca]


end AVRegularity.WeakEntryProofs
end
end

section
/-! General bounded transport preserves finite-window higher energy with divergence forcing. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CoupledEnergy.Variational

theorem molecularHigher_spatial_flux_energy (K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t (ξ : Vec 2), 3 / 4 * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j)
    (t : ℝ) (v : Vec 2 → Vec 2) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) v) (hp : AVenhance.IsZ2Periodic v)
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => v y k) x‖ ≤ Cv)
    (u S : TorusHk K ℂ) (F w : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ))) :
    2 * (-dataHigherDiffusion K ρ G t w -
      inner ℝ (factorialWeightedJet ρ (finiteTransport K v Cv hCv hv hp hb w).val)
        (factorialWeightedJet ρ u.val) +
      inner ℝ (factorialWeightedJet ρ S.val) (factorialWeightedJet ρ u.val) -
      inner ℝ (factorialWeightedJet ρ F.val) (factorialWeightedJet ρ w.val)) +
      factorialNormSq ρ w.val / 2 ≤
      (1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
        finiteTransportBudget (E := ℂ) K Cv j) ^ 2) * factorialNormSq ρ u.val +
        factorialNormSq ρ S.val + 4 * factorialNormSq ρ F.val := by
  let B := ∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
    finiteTransportBudget (E := ℂ) K Cv j
  have hT := (factorialPairing_abs_le ρ (finiteTransport K v Cv hCv hv hp hb w) u).trans
    (mul_le_mul_of_nonneg_right (finiteTransport_factorialNorm_le K v Cv hCv hv hp hb w ρ hρ)
      (Real.sqrt_nonneg _))
  change |inner ℝ _ _| ≤ B * Real.sqrt (factorialNormSq ρ w.val) *
    Real.sqrt (factorialNormSq ρ u.val) at hT
  have hU := Real.sq_sqrt (factorialNormSq_nonneg ρ u.val)
  have hW := Real.sq_sqrt (factorialNormSq_nonneg ρ w.val)
  have hS := Real.sq_sqrt (factorialNormSq_nonneg ρ S.val)
  have hF := Real.sq_sqrt (factorialNormSq_nonneg ρ F.val)
  exact finiteWindowFluxEnergy_normSq_arithmetic _ _ _ _ _ _ _ _ B _ _ _ _
    (dataHigherDiffusion_coercive K ρ G hG t w) hT
    (factorialPairing_abs_le ρ S u) (factorialPairing_abs_le ρ F w) hU hW hS hF

end AVRegularity.WeakEntryProofs
end
end

section
/-! Vanishing differentiated-equation residuals identify the actual finite-window trace derivative. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem molecularWeak_metric_quotient_tendsto {A : Type*} (l : Filter A)
    {a b : ℝ} (hab : a ≤ b) (P : MolecularData)
    (G : A → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (CG : A → ℝ)
    (hm : ∀ X i j, Measurable (fun t => G X t i j))
    (hb : ∀ X t i j, |G X t i j| ≤ CG X)
    (he : ∀ X t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G X t i j * ξ i * ξ j)
    (c : A → ℝ) (D : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (S : A → ℝ → ComplexCellL2) (S₀ S₁ : ℝ → ComplexCellL2)
    (F : A → ℝ → Fin 2 → ComplexCellL2) (F₀ F₁ : ℝ → Fin 2 → ComplexCellL2)
    (u : A → ℝ → ComplexCellL2) (v w : ℝ → ComplexCellL2)
    (slice : A → ℝ → TorusHk 1 ℂ) (other deriv : ℝ → TorusHk 1 ℂ)
    (h : ∀ X, CellWeakHilbertCurve a b (u X) (slice X) (fun t => dataDualDerivative
      (molecularMetricReplacement P (G X) (CG X) (hm X) (hb X) (he X)) t
        (slice X t) (S X t) (F X t)))
    (h₀ : CellWeakHilbertCurve a b v other
      (fun t => dataDualDerivative P t (other t) (S₀ t) (F₀ t)))
    (h₁ : CellWeakHilbertCurve a b w deriv (fun t => dataDualDerivative P t (deriv t)
      (S₁ t) (fun j => F₁ t j + molecularMetricHilbertFlux (D t) (other t) j)))
    (hS : ∀ X, MemLp (fun t => c X • (S X t - S₀ t) - S₁ t) 2
      (volume.restrict (Icc a b)))
    (hF : ∀ X j, MemLp (fun t => (c X • (F X t j - F₀ t j) - F₁ t j) +
      molecularMetricHilbertFlux (c X • (G X t - P.G t) - D t) (other t) j +
      molecularMetricHilbertFlux (G X t - P.G t) (deriv t) j) 2
        (volume.restrict (Icc a b)))
    (B : A → ℝ) (hB : ∀ X, 0 ≤ B X)
    (hbudget : ∀ X, ‖c X • (u X a - v a) - w a‖ ^ 2 + ∫ t in a..b,
      ‖c X • (S X t - S₀ t) - S₁ t‖ ^ 2 + 4 * ∑ j,
      ‖(c X • (F X t j - F₀ t j) - F₁ t j) +
        molecularMetricHilbertFlux (c X • (G X t - P.G t) - D t) (other t) j +
        molecularMetricHilbertFlux (G X t - P.G t) (deriv t) j‖ ^ 2 ≤ B X)
    (hsmall : Tendsto B l (𝓝 0)) (t : ℝ) (ht : t ∈ Icc a b) :
    Tendsto (fun X => c X • (u X t - v t) - w t) l (𝓝 0) := by
  let Q := fun X => molecularMetricReplacement P (G X) (CG X) (hm X) (hb X) (he X)
  have hd (X : A) := molecularWeak_metric_quotient_error a b P (G X) (CG X)
    (hm X) (hb X) (he X) (c X) (S X) S₀ S₁ (F X) F₀
    (fun t j => F₁ t j + molecularMetricHilbertFlux (D t) (other t) j)
    (u X) v w (slice X) other deriv (h X) h₀ h₁
  simp_rw [molecularMetricHilbertFlux_quotient_residual] at hd
  exact molecular_weak_window_value_tendsto_zero l hab Q P.V (fun _ => rfl)
    (fun X t => c X • (S X t - S₀ t) - S₁ t)
    (fun X t j => (c X • (F X t j - F₀ t j) - F₁ t j) +
      molecularMetricHilbertFlux (c X • (G X t - P.G t) - D t) (other t) j +
      molecularMetricHilbertFlux (G X t - P.G t) (deriv t) j)
    hS hF (fun X t => c X • (u X t - v t) - w t)
    (fun X t => c X • (slice X t - other t) - deriv t) hd B hB hbudget hsmall t ht

end AVRegularity.WeakEntryProofs
end
end

section
/-! Divergence and finite Pi synthesis preserve the local germs of actual mean coefficients. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftPiLeftTerms_slow_local_congr (Ω : Set (Vec 2)) (n : ℕ)
    (c d : LiftCoeff ι h) (t : ℝ)
    (he : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ X ∈ Ω, ∀ z v u,
      c m α t X z v u = d m α t X z v u) :
    List.Forall₂ (LeftTermSlowEq Ω) (liftPiLeftTerms n c t) (liftPiLeftTerms n d t) := by
  unfold liftPiLeftTerms
  apply leftTermSlowEq_flatMap_same
  intro v _
  exact List.rel_map (fun _ _ hh => hh.postcompose (ContinuousLinearMap.single ℝ h v))
    (liftComponentLeftTerms_slow_local_congr n c d t v
      (fun m hm α X hX z u => he m hm α X hX z v u))

theorem leftTermsSlowPartial_slow_local_congr {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (k : Fin 2)
    (l r : List (LeftTerm E F)) (he : List.Forall₂ (LeftTermSlowEq Ω) l r) :
    List.Forall₂ (LeftTermSlowEq Ω) (leftTermsSlowPartial k l) (leftTermsSlowPartial k r) := by
  exact covariantLeftTermList_slow_local_congr hΩ 1
    (List.ofFn (fun _ : Fin 1 => k)) l r he 1

theorem meanFluxLeftTerms_slow_local_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (n : ℕ) (C E : Fin 2 → LiftCoeff ι h) (t : ℝ)
    (he : ∀ k m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ X ∈ Ω, ∀ v u,
      C k m α t X 0 v u = E k m α t X 0 v u) :
    List.Forall₂ (LeftTermSlowEq Ω) (meanFluxLeftTerms n C t) (meanFluxLeftTerms n E t) := by
  unfold meanFluxLeftTerms
  apply leftTermSlowEq_flatMap_same
  intro k _
  apply leftTermsSlowPartial_slow_local_congr Ω hΩ k
  apply liftPiLeftTerms_slow_local_congr Ω (n - 1)
  intro m hm α X hX _ v u
  exact he k m hm α X hX v u

end AVRegularity.WeakEntryProofs
end
end
end
