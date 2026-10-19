-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.SlowBasisProjectionBound
public import AVRegularity.CycleWords.GeometryScalarComponentFlux
public import AVRegularity.CycleEvolution.CellComplexH1Carrier

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Spatially constant cell metrics have no differentiated metric source. -/

section
open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem metricCommutatorTerm_constant {K j : ℕ} (hj : j ≤ K)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (D : RawJet2 (K + 1) E)
    (w : DerivativeWord2 j) (x : Vec 2) :
    metricCommutatorTerm hj (fun _ => G) D w x = 0 := by
  classical
  unfold metricCommutatorTerm
  apply Finset.sum_eq_zero
  intro m _
  split_ifs with hm
  · unfold metricMaskTerm
    have hz : (fun k a => orderedScalarDerivative (fun _ : Vec 2 => G k a)
        (maskLeftLength j m) (maskWordEquiv 2 j m w).1 x) = 0 := by
      funext k a
      rw [orderedScalarDerivative_eq_iterated _ _ contDiff_const]
      rw [iteratedFDeriv_const_of_ne (by omega)]
      rfl
    rw [hz]
    ext k
    simp [finiteMetricFlux]
  · rfl
end

/-! Metric word insertion constants are independent of the fibre dimension. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem metricWordEntry_norm_le_one {a b : ι} (m : ℕ) (hab : a = b) (hm : m = 1)
    (k j : Fin 2) : ‖Weighted.metricWordEntry (h := h) m hab hm k j‖ ≤ 1 := by
  subst hab hm
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro U
  have he : Weighted.metricWordEntry (h := h) 1 rfl rfl k j U =
      PiLp.single 2 k (U (fun _ => j)) := by
    apply PiLp.ext
    intro i
    fin_cases i <;> fin_cases k <;> fin_cases j <;>
      simp [Weighted.metricWordEntry, metricFlux, Matrix.single, Fin.sum_univ_two]
  rw [he, PiLp.norm_single, one_mul]
  exact PiLp.norm_apply_le _ _
end

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The native geometry chain has the same scalar equation for every reserve D ≥ 2. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem geometryScalarFlux_eq_order_two (D : ℕ) (hD : 2 ≤ D)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (κ : Fin 1 → ι → ℕ)
    (w : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin 1 × ι) (t : ℝ) :
    geometryScalarFlux D G κ w i t = Weighted.scalarChainFlux G κ w i t := by
  funext z
  apply PiLp.ext
  intro k
  rw [geometryScalarFlux_eq D hD, Weighted.scalarChainFlux_eq]

theorem geometryScalarSolution_order_two (D : ℕ) (hD : 2 ≤ D)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (κ : Fin 1 → ι → ℕ)
    (a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ j x, PlaneHk Set.univ (κ j x) (h x))
    (F : ∀ j x, ℝ → PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (u : ∀ j x, ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ j x, ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hsln : IsPlaneChainFrom (geometryScalarData D G) κ a b v f F u w) :
    IsPlaneChainFrom (geometryScalarData 2 G) κ a b v f F u w := by
  refine ⟨hsln.1, hsln.2.1, hsln.2.2.1, hsln.2.2.2.1, ?_⟩
  intro i t ht φ
  have he := hsln.2.2.2.2 i t ht φ
  change CoupledWeakIdentity _ _ _ _ _ _ _ _ _ _
    (fun s => geometryScalarFlux D G κ (fun p => w p.1 p.2 s) i s) _ _ at he
  change CoupledWeakIdentity _ _ _ _ _ _ _ _ _ _
    (fun s => Weighted.scalarChainFlux G κ (fun p => w p.1 p.2 s) i s) _ _
  simpa only [geometryScalarFlux_eq_order_two D hD] using he

theorem geometryScalarSolution_singleton_order_two (D : ℕ) (hD : 2 ≤ D)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (K : ι → ℕ)
    (a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (F : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (u : ∀ (_ : Fin 1) x, ℝ → PlaneHk Set.univ (K x) (h x))
    (w : ∀ (_ : Fin 1) x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (hsln : IsPlaneChainFrom (geometryScalarData D G) (fun _ x => K x) a b v
      (fun _ x => f x) (fun _ x => F x) u w) :
    IsPlaneChainFrom (geometryScalarData 2 G) (fun _ x => K x) a b v
      (fun _ x => f x) (fun _ x => F x) (fun _ x => u 0 x) (fun _ x => w 0 x) := by
  have hh := geometryScalarSolution_order_two D hD G (fun _ x => K x) a b v
    (fun _ x => f x) (fun _ x => F x) u w hsln
  have hu : u = fun _ x => u 0 x := by
    funext j x
    rw [Fin.eq_zero j]
  have hw : w = fun _ x => w 0 x := by
    funext j x
    rw [Fin.eq_zero j]
  rw [hu, hw] at hh
  exact hh

end AVRegularity.CycleWords
end

section
open MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Countable topology of the actual complex periodic H1 graph and its L2 fields. -/

instance cellComplexH1_secondCountable : SecondCountableTopology CellComplexH1 := by
  let : SecondCountableTopology (ComponentL2 (volume.restrict AVenhance.unitCube) ℂ) :=
    AVRegularity.CoupledEnergy.Variational.cellL2SecondCountableTopology
  let : SecondCountableTopology (JetL2 (volume.restrict AVenhance.unitCube) 1 ℂ) :=
    PiLp.secondCountableTopology 2 _
  infer_instance

theorem cellComplexH1LpSecondCountable {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] (μ : Measure X) [SFinite μ] :
    SecondCountableTopology (Lp CellComplexH1 2 μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : TopologicalSpace.SeparableSpace CellComplexH1 := inferInstance
  exact Lp.SecondCountableTopology

end AVRegularity.CycleWords
end
