-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.PositiveCutoffMetricEllipticity
import AVRegularity.EntryWeakAssembly.WindowListL2Representative
public import AVRegularity.EntryWeak.IndependentCenteredChildReanchorCoordinates
import AVRegularity.Proofs.GenSem.ChainMetric
import AVRegularity.Construction.Uniqueness.SuccessorFluxUnique

@[expose] public noncomputable section

section
namespace AVRegularity.WeakEntryProofs

/-! Finitely many local inverse reserves admit one common actual coefficient cutoff. -/

section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.EntryWeakProofs
variable {I E : Type*} [Fintype I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {H : ℕ}

theorem finite_local_window_cutoff_reserves (a b : ℝ) (hab : a ≤ b)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (Y₀ : Vec 2) (hYΩ : Y₀ ∈ Ω)
    (f : I → ℝ → Vec 2 → Vec 2 → E)
    (hz : ∀ i Y, Y ∈ Ω → ∀ z, f i a z Y = 0)
    (hloc : ∀ i, ∃ (U : Set (Vec 2)) (f' : ℝ → Vec 2 → Vec 2 → E),
      IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve H
        (independentTimeWindowSource (Ioc a b) f')) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, f' t z Y = f i t z Y) :
    ∃ (χ : Vec 2 → ℝ), tsupport χ ⊆ Ω ∧ χ =ᶠ[𝓝 Y₀] 1 ∧
      Nonempty (∀ i, JointSourceReserve H
        (fun t z Y => χ Y • f i (max a (min b t)) z Y)) := by
  classical
  choose U f' hU hY hR he using hloc
  let V := Ω ∩ ⋂ i, U i
  have hV : IsOpen V := hΩ.inter (isOpen_iInter_of_finite hU)
  have hYV : Y₀ ∈ V := ⟨hYΩ, mem_iInter.mpr hY⟩
  obtain ⟨χ, Qχ, hχ, hone⟩ := local_slow_cutoff_reserve_exists H V hV Y₀ hYV
  refine ⟨χ, (fun Y hY => (hχ hY).1), hone, ?_⟩
  refine ⟨fun i => jointReserveOfIndependent (localWindowCutoffReserve a b hab V χ hχ
    (independentReserveOfJoint Qχ) (f i) (f' i) (Classical.choice (hR i)) ?_ ?_)⟩
  · intro t ht Y hY z
    exact he i t ht Y (mem_iInter.mp hY.2 i) z
  · intro Y hY z
    exact hz i Y hY.1 z
end

/-! Symmetry of the primitive metric is preserved by every genuine parameter word. -/

section
open Homogenization AVRegularity.EntryWeakProofs

theorem coordinate_metric_word_symm {d : ℕ}
    (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (hs : ∀ t Y, (G t Y).IsSymm) (w : List (Fin d)) (Y : Vec d) (t : ℝ) :
    (independentMetricWordJet G w.length (coordinateWordDirections w) Y t).IsSymm := by
  ext i j
  change iteratedFDeriv ℝ w.length (fun X => G t X j i) Y (coordinateWordDirections w) =
    iteratedFDeriv ℝ w.length (fun X => G t X i j) Y (coordinateWordDirections w)
  have he : (fun X => G t X j i) = fun X => G t X i j :=
    funext (fun X => congrFun (congrFun (hs t X) i) j)
  rw [he]
end

/-! A compact slow cutoff gives finite global jets on a fixed clock window for an arbitrary smooth metric. -/

section
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open scoped ContDiff
variable {d : ℕ}

theorem compact_cutoff_metric_jet_budget
    (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × Vec d => G p.1 p.2 i j))
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (S : Set (Vec d)) (hS : IsCompact S) (hs : tsupport χ ⊆ S) (a b : ℝ) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ n t, t ∈ Icc a b → ∀ Y i j,
      ‖iteratedFDeriv ℝ n (fun X => cutoffParameterMetric χ G t X i j) Y‖ ≤ B n := by
  have hb i j := compact_spacetime_slow_jet_budget
    (fun p : ℝ × Vec d => G p.1 p.2 i j) (hG i j) a b S hS
  choose B hB hb using hb
  let C := fun n => ∑ i : Fin 2, ∑ j : Fin 2, B i j n
  have hC n : 0 ≤ C n := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hB i j n))
  have hBC i j n : B i j n ≤ C n :=
    (Finset.single_le_sum (fun k _ => hB i k n) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hB k l n)) (Finset.mem_univ i))
  have hA (n : ℕ) : ∃ A : ℝ, ∀ Y, ‖iteratedFDeriv ℝ n χ Y‖ ≤ A :=
    (hcχ.iteratedFDeriv n).exists_bound_of_continuous
      (ContDiff.continuous_iteratedFDeriv (m := n) (by simp) hχ)
  choose A hA using hA
  have hAn n : 0 ≤ A n := (norm_nonneg _).trans (hA n 0)
  refine ⟨independentCutoffUnitBudget ℝ A C,
    independentCutoffUnitBudget_nonneg A C hAn hC, ?_⟩
  intro n t ht Y i j
  have hreg : ContDiff ℝ ∞ (fun X => G t X i j) :=
    (hG i j).comp₂ contDiff_const contDiff_id
  have he : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) i j‖ ≤ 1 := by
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  exact independentCutoffExtension_jet_bound_one χ (fun X => G t X i j) _ he n n
    (hχ.of_le (by simp)) (hreg.of_le (by simp)) le_rfl S hs A C hAn hC
    (fun k _ => hA k) (fun k _ X hX => (hb i j k t ht X hX).trans (hBC i j k)) Y
end

/-! Genuine coordinate source words commute with bounded linear readouts. -/

section
open Homogenization AVRegularity.EntryWeakProofs
open scoped ContDiff
variable {d H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [BorelSpace E] [SecondCountableTopology E] in
theorem coordinate_source_word_map {f : ℝ → Vec 2 → Vec d → E}
    (Q : IndependentParameterSourceReserve H f) (L : E →L[ℝ] ℂ)
    (w : List (Fin d)) (hw : w.length ≤ H) (Y : Vec d) (t : ℝ) (z : Vec 2) :
    coordinateSourceWord (fun s x X => L (f s x X)) w Y t z =
      L (coordinateSourceWord f w Y t z) := by
  have hr : ContDiff ℝ (H : ℕ∞) (f t z) :=
    (Q.regular t).comp₂ contDiff_const contDiff_id
  have he := L.iteratedFDeriv_comp_left (hr.contDiffAt (x := Y))
    (i := w.length) (by exact_mod_cast hw)
  exact congrArg (fun A => A (coordinateWordDirections w)) he
end

/-! Primitive joint reserves give finite-window Hilbert Taylor remainder convergence. -/

section
open MeasureTheory Homogenization AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution
open Set Filter Topology

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

omit [BorelSpace E] [SecondCountableTopology E] in
theorem independent_source_quotient_pointwise_bound {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (hH : 2 ≤ H) (Y v : P)
    (h : ℝ) (hh : h ≠ 0) (t : ℝ) (z : Vec 2) :
    ‖h⁻¹ • (f t z (Y + h • v) - f t z Y) - fderiv ℝ (f t z) Y v‖ ≤
      Q.budget 2 * |h| * ‖v‖ ^ 2 := by
  have hr : ContDiff ℝ ((2 : ℕ) : ℕ∞) (fun Z : Vec 2 × P => f t Z.1 Z.2) :=
    (Q.regular t).of_le (by exact_mod_cast hH)
  apply independent_parameter_quotient_bound (f t z)
    (hr.comp₂ contDiff_const contDiff_id) (Q.budget 2) (Q.budget_nonneg 2) _ Y v h hh
  intro X
  have hb := Q.parameter_derivative_bound 2 hH t z X
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at hb
  exact hb

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] in
theorem independent_source_window_quotient_energy_tendsto_zero
    {H : ℕ} {f : ℝ → Vec 2 → P → ℂ}
    (Q : IndependentParameterSourceReserve H f) (hH : 2 ≤ H)
    {a b : ℝ} (hab : a ≤ b) (Y v : P) :
    Tendsto (fun h : ℝ => ∫ t in a..b,
      ‖cellSourceSlice (fun s z => h⁻¹ • (f s z (Y + h • v) - f s z Y) -
        fderiv ℝ (f s z) Y v) t‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  let e := fun (h s : ℝ) (z : Vec 2) => h⁻¹ • (f s z (Y + h • v) - f s z Y) - fderiv ℝ (f s z) Y v
  have hm (h : ℝ) : Measurable (Function.uncurry (e h)) :=
    ((((Q.measurable (Y + h • v)).sub (Q.measurable Y)).const_smul h⁻¹).sub
      (Q.directional_derivative_measurable (by omega) Y v))
  have he (h : ℝ) : MemLp (Function.uncurry (e h)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) :=
    ((((independent_source_window_memLp Q a b (Y + h • v)).sub
      (independent_source_window_memLp Q a b Y)).const_smul h⁻¹).sub
        (independent_source_directional_window_memLp Q (by omega) a b Y v))
  let C := fun h : ℝ => Q.budget 2 * |h| * ‖v‖ ^ 2
  have hC : ∀ᶠ h : ℝ in 𝓝[≠] 0, 0 ≤ C h := Eventually.of_forall (fun h => by
    dsimp only [C]
    exact mul_nonneg (mul_nonneg (Q.budget_nonneg 2) (abs_nonneg h)) (sq_nonneg _))
  have hb : ∀ᶠ h : ℝ in 𝓝[≠] 0, ∀ t z, ‖e h t z‖ ≤ C h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact fun t z => independent_source_quotient_pointwise_bound Q hH Y v h hh t z
  have hc : Tendsto C (𝓝[≠] 0) (𝓝 0) := by
    have hh : Continuous C := by dsimp only [C]; fun_prop
    simpa only [C, abs_zero, mul_zero, zero_mul] using
      (hh.tendsto 0).mono_left nhdsWithin_le_nhds
  exact cellSourceSlice_window_integral_tendsto_zero (𝓝[≠] 0) hab e hm he C hC hb hc
end

/-! Primitive metric coordinate words have their genuine parameter derivatives without normalization. -/

section
open Homogenization MeasureTheory
open AVRegularity.EntryWeakProofs
open scoped ContDiff
variable {d H : ℕ} {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}

theorem coordinate_metric_word_parameter_regular
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (w : List (Fin d)) (R : ℕ) (t : ℝ) (i j : Fin 2) :
    ContDiff ℝ (R : ℕ∞) (fun X =>
      independentMetricWordJet G w.length (coordinateWordDirections w) X t i j) :=
  finite_realWordJet_contDiff (fun X => G t X i j) w.length R
    ((hr t i j).of_le (by simp)) (coordinateWordDirections w)

theorem coordinate_metric_word_parameter_cons
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (w : List (Fin d)) (i : Fin d) (t : ℝ) (Y : Vec d) :
    independentMetricWordJet G (i :: w).length (coordinateWordDirections (i :: w)) Y t =
      Matrix.of (fun j k => fderiv ℝ
        (fun X => independentMetricWordJet G w.length (coordinateWordDirections w) X t j k) Y (basisVec i)) := by
  apply Matrix.ext
  intro j k
  change realWordJet (fun X => G t X j k) (w.length + 1)
    (coordinateWordDirections (i :: w)) Y = _
  rw [coordinateWordDirections_cons]
  exact general_metric_word_cons hr w.length (coordinateWordDirections w) (basisVec i) Y t j k

theorem coordinate_metric_word_parameter_second_bound
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (B : ℕ → ℝ)
    (hb : ∀ n, n ≤ H → ∀ t Y i j,
      ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n)
    (w : List (Fin d)) (hw : w.length + 2 ≤ H) (t : ℝ) (i j : Fin 2) (Y : Vec d) :
    ‖fderiv ℝ (fderiv ℝ (fun X =>
      independentMetricWordJet G w.length (coordinateWordDirections w) X t i j)) Y‖ ≤ B (w.length + 2) := by
  have hh := general_metric_word_derivative_bound hr B hb w.length 2 hw
    (coordinateWordDirections w) (coordinateWordDirections_norm w) Y t i j
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at hh
  exact hh
end

/-! Primitive source Taylor bounds hold for the literal Hilbert difference quotients in the weak equation. -/

section
open MeasureTheory Homogenization AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution
open Set Filter Topology

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_source_slice_quotient_eq {H : ℕ} {f : ℝ → Vec 2 → P → ℂ}
    (Q : IndependentParameterSourceReserve H f) (hH : 1 ≤ H) (Y v : P) (h t : ℝ) :
    cellSourceSlice (fun s z => h⁻¹ • (f s z (Y + h • v) - f s z Y) -
      fderiv ℝ (f s z) Y v) t =
      h⁻¹ • (cellSourceSlice (fun s z => f s z (Y + h • v)) t -
        cellSourceSlice (fun s z => f s z Y) t) -
          cellSourceSlice (fun s z => fderiv ℝ (f s z) Y v) t := by
  have hp := independent_source_slice_memLp Q t (Y + h • v)
  have hz := independent_source_slice_memLp Q t Y
  have hd := independent_source_directional_slice_memLp Q hH t Y v
  rw [cellSourceSlice_sub_of_memLp _ _ t ((hp.sub hz).const_smul h⁻¹) hd,
    cellSourceSlice_smul_of_memLp _ t h⁻¹ (hp.sub hz),
    cellSourceSlice_sub_of_memLp _ _ t hp hz]

theorem independent_source_slice_window_quotient_energy_tendsto_zero
    {H : ℕ} {f : ℝ → Vec 2 → P → ℂ}
    (Q : IndependentParameterSourceReserve H f) (hH : 2 ≤ H)
    {a b : ℝ} (hab : a ≤ b) (Y v : P) :
    Tendsto (fun h : ℝ => ∫ t in a..b,
      ‖h⁻¹ • (cellSourceSlice (fun s z => f s z (Y + h • v)) t -
        cellSourceSlice (fun s z => f s z Y) t) -
          cellSourceSlice (fun s z => fderiv ℝ (f s z) Y v) t‖ ^ 2)
        (𝓝[≠] 0) (𝓝 0) := by
  have hh := independent_source_window_quotient_energy_tendsto_zero Q hH hab Y v
  simp_rw [independent_source_slice_quotient_eq Q (by omega) Y v] at hh
  exact hh
end

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVenhance.Infra.ODE
namespace AVRegularity.WeakEntryProofs

/-! The finite-window higher flux estimate applies to every actual molecular raw solution. -/

open AVRegularity.EntryWeakProofs

theorem molecular_actual_flux_higher_window_trace_bound {a b : ℝ} (hlt : a < b)
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (hsm : Measurable (Function.uncurry src))
    (hfm : Measurable (Function.uncurry flux))
    (hsp : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hfp : MemLp (Function.uncurry flux) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀)
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : factorialNormSq 1 u₀.val + ∫ s in a..b,
      factorialNormSq 1 (S s).val + 4 * factorialNormSq 1 (F s).val ≤ B)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (dataCoefficients P) src flux D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] initial) :
    ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ,
      torusHkValueCLM w = cellRawTrace D t ∧
        ‖w‖ ≤ Real.sqrt ((B * Real.exp ((1 + 4 *
          (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
            finiteTransportBudget (E := ℂ) K Cv j) ^ 2) * (b - a))) / factorialWeightMin 1 K) := by
  obtain ⟨u, slice, _, hU, hu0, hbnd⟩ := molecular_regular_flux_exists_window_bound hlt
    hsm hfm hsp hfp K Cv hCv hv hp hb S hs F hS hF hf
    u₀ hinit B hB hbudget
  obtain ⟨R, hR, htrace⟩ := dataWeakHilbert_exists_raw_solution P src flux hsp hfp
    u slice hU
  have hri : cellValue R a =ᵐ[volume.restrict AVenhance.unitCube] initial :=
    (htrace a).symm.trans (Filter.EventuallyEq.of_eq
      (congrArg (fun z : ComplexCellL2 => (z : Vec 2 → ℂ)) hu0))
  have hu := dataActual_unique_raw hlt.le P src flux hsp hfp D R hD hR (hi.trans hri.symm)
  intro t ht
  obtain ⟨w, hw, hn⟩ := hbnd t ht
  refine ⟨w, hw.trans ?_, hn⟩
  apply Lp.ext
  exact (htrace t).trans ((hu t ht).symm.trans
    (cellRawTrace_ae D t (hD.2.2.1 t ht).1).symm)

end AVRegularity.WeakEntryProofs
end

section
namespace AVRegularity.WeakEntryProofs

/-! Primitive source Lipschitz bounds give continuity of the actual finite-window Hilbert forcing. -/

section
open MeasureTheory Homogenization AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution
open Set Filter Topology

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_source_slice_window_difference_energy_tendsto_zero
    {H : ℕ} {f : ℝ → Vec 2 → P → ℂ}
    (Q : IndependentParameterSourceReserve H f) (hH : 1 ≤ H)
    {a b : ℝ} (hab : a ≤ b) (Y : P) :
    Tendsto (fun X => ∫ t in a..b,
      ‖cellSourceSlice (fun s z => f s z X) t -
        cellSourceSlice (fun s z => f s z Y) t‖ ^ 2) (𝓝 Y) (𝓝 0) := by
  let e := fun X s z => f s z X - f s z Y
  let C := fun X => Q.budget 1 * ‖X - Y‖
  have hm (X : P) : Measurable (Function.uncurry (e X)) :=
    (Q.measurable X).sub (Q.measurable Y)
  have he (X : P) : MemLp (Function.uncurry (e X)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) :=
    (independent_source_window_memLp Q a b X).sub (independent_source_window_memLp Q a b Y)
  have hC : ∀ᶠ X in 𝓝 Y, 0 ≤ C X := Eventually.of_forall (fun X =>
    mul_nonneg (Q.budget_nonneg 1) (norm_nonneg (X - Y)))
  have hb : ∀ᶠ X in 𝓝 Y, ∀ t z, ‖e X t z‖ ≤ C X :=
    Eventually.of_forall (fun X t z => Q.parameter_lipschitz hH t z Y X)
  have hc : Tendsto C (𝓝 Y) (𝓝 0) := by
    have hh : Continuous C := by dsimp only [C]; fun_prop
    simpa only [C, sub_self, norm_zero, mul_zero] using hh.tendsto Y
  have ht := cellSourceSlice_window_integral_tendsto_zero (𝓝 Y) hab e hm he C hC hb hc
  have hid (X : P) (t : ℝ) : cellSourceSlice (e X) t =
      cellSourceSlice (fun s z => f s z X) t - cellSourceSlice (fun s z => f s z Y) t :=
    cellSourceSlice_sub_of_memLp _ _ t
      (independent_source_slice_memLp Q t X) (independent_source_slice_memLp Q t Y)
  simpa only [hid] using ht
end

/-! The literal source Taylor residual is square integrable on every finite window. -/

section
open MeasureTheory Homogenization AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution Set
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem independent_source_slice_window_quotient_memLp {H : ℕ}
    {f : ℝ → Vec 2 → A → ℂ} (Q : IndependentParameterSourceReserve H f)
    (hH : 1 ≤ H) (a b : ℝ) (Y v : A) (h : ℝ) :
    MemLp (fun t => h⁻¹ •
      (cellSourceSlice (fun s z => f s z (Y + h • v)) t -
        cellSourceSlice (fun s z => f s z Y) t) -
          cellSourceSlice (fun s z => fderiv ℝ (f s z) Y v) t)
      2 (volume.restrict (Icc a b)) :=
  (((cellSourceSlice_memLp (Icc a b) (fun s z => f s z (Y + h • v))
    (independent_source_window_memLp Q a b (Y + h • v))).sub
      (cellSourceSlice_memLp (Icc a b) (fun s z => f s z Y)
        (independent_source_window_memLp Q a b Y))).const_smul h⁻¹).sub
    (cellSourceSlice_memLp (Icc a b) (fun s z => fderiv ℝ (f s z) Y v)
      (independent_source_directional_window_memLp Q hH a b Y v))
end

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVenhance.Infra.ODE
namespace AVRegularity.WeakEntryProofs

/-! Finite-window higher flux bounds do not depend on a measurable raw representative. -/

section
open AVRegularity.EntryWeakProofs

theorem molecular_actual_flux_higher_window_trace_bound_ae {a b : ℝ} (hlt : a < b)
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (hsp : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hfp : MemLp (Function.uncurry flux) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀)
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : factorialNormSq 1 u₀.val + ∫ s in a..b,
      factorialNormSq 1 (S s).val + 4 * factorialNormSq 1 (F s).val ≤ B)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (dataCoefficients P) src flux D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] initial) :
    ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ,
      torusHkValueCLM w = cellRawTrace D t ∧
        ‖w‖ ≤ Real.sqrt ((B * Real.exp ((1 + 4 *
          (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
            finiteTransportBudget (E := ℂ) K Cv j) ^ 2) * (b - a))) / factorialWeightMin 1 K) := by
  let sm := hsp.aestronglyMeasurable.mk (Function.uncurry src)
  let src' := fun t x => sm (t, x)
  have hes : Function.uncurry src =ᵐ[
      (volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)]
      Function.uncurry src' := hsp.aestronglyMeasurable.ae_eq_mk
  have hsm : Measurable (Function.uncurry src') :=
    hsp.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hsp' := hsp.ae_eq hes
  have hscalar := cellSourceSlice_congr_ae (Icc a b) src src' hsp hsp' hes
  have hs' : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src' t := by
    filter_upwards [hs, hscalar] with t ht he
    exact ht.trans he
  let m := hfp.aestronglyMeasurable.mk (Function.uncurry flux)
  let flux' := fun t x => m (t, x)
  have he : Function.uncurry flux =ᵐ[
      (volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)]
      Function.uncurry flux' := hfp.aestronglyMeasurable.ae_eq_mk
  have hfm : Measurable (Function.uncurry flux') :=
    hfp.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfp' := hfp.ae_eq he
  have hsec := Measure.ae_ae_of_ae_prod he
  have hcoord (j : Fin 2) : cellSourceSlice (fun s x => flux s x j) =ᵐ[
      volume.restrict (Icc a b)] cellSourceSlice (fun s x => flux' s x j) :=
    cellSourceSlice_congr_ae (Icc a b) _ _
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hfp)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hfp')
      (he.fun_comp (fun v => v j))
  have hf' : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux' s x j) t := by
    filter_upwards [hf, (Filter.eventually_all_finset (Finset.univ : Finset (Fin 2))).2 (fun j _ => hcoord j)] with t ht heq
    intro j
    exact (ht j).trans (heq j (Finset.mem_univ j))

  have hD' := cellSolution_source_congr_sections (Icc a b) (dataCoefficients P)
    src src' flux flux' D (Measure.ae_ae_of_ae_prod hes) hsec hD
  exact molecular_actual_flux_higher_window_trace_bound hlt hsm hfm hsp' hfp'
    K Cv hCv hv hp hb S hs' F hS hF hf' u₀ hinit B hB hbudget D hD' hi
end

/-! Literal higher carrier readouts supply the general finite-window flux bound. -/

section
open AVRegularity.EntryWeakProofs

theorem molecular_actual_flux_higher_window_carrier_bound {a b : ℝ} (hlt : a < b)
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (hsp : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hfp : MemLp (Function.uncurry flux) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      torusHkValueCLM (S t) =ᵐ[volume.restrict AVenhance.unitCube] src t)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b),
      torusHkValueCLM (F t) =ᵐ[volume.restrict AVenhance.unitCube] flux t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀)
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : factorialNormSq 1 u₀.val + ∫ s in a..b,
      factorialNormSq 1 (S s).val + 4 * factorialNormSq 1 (F s).val ≤ B)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (dataCoefficients P) src flux D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] initial) :
    ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ,
      torusHkValueCLM w = cellRawTrace D t ∧
        ‖w‖ ≤ Real.sqrt ((B * Real.exp ((1 + 4 *
          (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
            finiteTransportBudget (E := ℂ) K Cv j) ^ 2) * (b - a))) / factorialWeightMin 1 K) := by
  have hs' : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src t := by
    filter_upwards [hs] with t ht
    exact (cellSourceSlice_eq_of_ae src t (torusHkValueCLM (S t)) ht).symm
  have hf' : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t := by
    filter_upwards [hf] with t ht
    intro j
    apply (cellSourceSlice_eq_of_ae _ t _ ?_).symm
    exact (ContinuousLinearMap.coeFn_compLpL
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j) (torusHkValueCLM (F t))).trans
      (ht.fun_comp (fun v => v j))
  exact molecular_actual_flux_higher_window_trace_bound_ae hlt hsp hfp K Cv hCv
    hv hp hb S hs' F hS hF hf' u₀ hinit B hB hbudget D hD hi
end

end AVRegularity.WeakEntryProofs
end

section
namespace AVRegularity.WeakEntryProofs

/-! Positive constant clock scaling normalizes a full parameter metric without upper normalization. -/

section
open Homogenization MeasureTheory
open scoped ContDiff
variable {d : ℕ}

def clockParameterMetric (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ)
    (t : ℝ) (Y : Vec d) : Matrix (Fin 2) (Fin 2) ℝ := c • G (c * t) Y

theorem clockParameterMetric_regular (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ)
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j)) (t : ℝ) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun X => clockParameterMetric G c t X i j) :=
  (hr (c * t) i j).const_smul c

theorem clockParameterMetric_measurable (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ)
    (hm : ∀ Y i j, Measurable (fun t => G t Y i j)) (Y : Vec d) (i j : Fin 2) :
    Measurable (fun t => clockParameterMetric G c t Y i j) :=
  measurable_const.mul ((hm Y i j).comp (measurable_const.mul measurable_id))

theorem clockParameterMetric_jet_bound (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (c : ℝ) (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (B : ℕ → ℝ) (hb : ∀ n t Y i j, ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n)
    (n : ℕ) (t : ℝ) (Y : Vec d) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun X => clockParameterMetric G c t X i j) Y‖ ≤ |c| * B n := by
  change ‖iteratedFDeriv ℝ n (fun X => c • G (c * t) X i j) Y‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((hr (c * t) i j).of_le (by simp)).contDiffAt,
    norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hb n (c * t) Y i j) (abs_nonneg c)

theorem clockParameterMetric_coercive (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (lo : ℝ) (hlo : 0 < lo)
    (he : ∀ t Y (ξ : Vec 2), lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t Y i j * ξ i * ξ j)
    (Y : Vec d) (t : ℝ) (ξ : Vec 2) :
    (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, clockParameterMetric G lo⁻¹ t Y i j * ξ i * ξ j := by
  have hs : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (he (lo⁻¹ * t) Y ξ) (inv_nonneg.mpr hlo.le)
  rw [← mul_assoc, inv_mul_cancel₀ hlo.ne', one_mul] at hh
  have hlow : (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ξ i ^ 2 := by linarith only [hs]
  apply (hlow.trans hh).trans_eq
  simp only [clockParameterMetric, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end

/-! Metric Taylor remainders converge in the finite-window divergence forcing energy without upper ellipticity normalization. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem parameter_metric_directional_measurable
    (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ)
    (hr : ∀ t i j, ContDiff ℝ 1 (fun X => G t X i j))
    (hm : ∀ X i j, Measurable (fun t => G t X i j)) (Y v : P) (i j : Fin 2) :
    Measurable (fun t => fderiv ℝ (fun X => G t X i j) Y v) := by
  have hh := finite_independentParameterWordJet_measurable (fun t X => G t X i j) 1
    (fun t => hr t i j) (fun X => hm X i j) (fun _ : Fin 1 => v) Y
  simpa only [realWordJet, iteratedFDeriv_one_apply] using hh

theorem parameter_metric_window_quotient_flux_energy_tendsto_zero
    (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ)
    (hr : ∀ t i j, ContDiff ℝ 2 (fun X => G t X i j))
    (hm : ∀ X i j, Measurable (fun t => G t X i j))
    (C : ℝ) (hC : 0 ≤ C)
    (hD : ∀ t i j X, ‖fderiv ℝ (fderiv ℝ (fun Y => G t Y i j)) X‖ ≤ C)
    {a b : ℝ} (hab : a ≤ b) (Y v : P)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 (volume.restrict (Icc a b))) (k : Fin 2) :
    Tendsto (fun h : ℝ => ∫ t in a..b,
      ‖molecularMetricHilbertFlux
        (h⁻¹ • (G t (Y + h • v) - G t Y) -
          Matrix.of (fun i j => fderiv ℝ (fun X => G t X i j) Y v)) (u t) k‖ ^ 2)
        (𝓝[≠] 0) (𝓝 0) := by
  let M := fun (h t : ℝ) => h⁻¹ • (G t (Y + h • v) - G t Y) -
    Matrix.of (fun i j => fderiv ℝ (fun X => G t X i j) Y v)
  let δ := fun h : ℝ => C * |h| * ‖v‖ ^ 2
  have hM (h : ℝ) (i j : Fin 2) : Measurable (fun t => M h t i j) := by
    exact ((measurable_const : Measurable (fun _ : ℝ => h⁻¹)).mul
      ((hm (Y + h • v) i j).sub (hm Y i j))).sub
        (parameter_metric_directional_measurable G (fun t i j => (hr t i j).of_le (by norm_num)) hm Y v i j)
  have hb : ∀ᶠ h : ℝ in 𝓝[≠] 0, ∀ t i j, |M h t i j| ≤ δ h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    intro t i j
    exact independent_parameter_quotient_bound (fun X => G t X i j)
      (hr t i j) C hC (hD t i j) Y v h hh
  have hδ : Tendsto δ (𝓝[≠] 0) (𝓝 0) := by
    have hd : Continuous δ := by dsimp only [δ]; fun_prop
    simpa only [δ, abs_zero, mul_zero, zero_mul] using
      (hd.tendsto 0).mono_left nhdsWithin_le_nhds
  exact molecularMetricHilbertFlux_component_integral_tendsto_zero_of_eventually_bound
    (𝓝[≠] 0) hab M δ hM hb u hu hδ k
end

/-! Genuine primitive coordinate words supply all finite-window source Taylor residuals. -/

section
open MeasureTheory Homogenization Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution
variable {d H : ℕ}

theorem coordinate_source_word_slice_window_taylor {f : ℝ → Vec 2 → Vec d → ℂ}
    (Q : IndependentParameterSourceReserve H f) (w : List (Fin d))
    (hw : w.length + 2 ≤ H) {a b : ℝ} (hab : a ≤ b) (Y : Vec d) (i : Fin d) :
    (∀ h : ℝ, MemLp (fun t => h⁻¹ •
      (cellSourceSlice (coordinateSourceWord f w (Y + h • basisVec i)) t -
        cellSourceSlice (coordinateSourceWord f w Y) t) -
          cellSourceSlice (coordinateSourceWord f (i :: w) Y) t)
      2 (volume.restrict (Icc a b))) ∧
    Tendsto (fun h : ℝ => ∫ t in a..b, ‖h⁻¹ •
      (cellSourceSlice (coordinateSourceWord f w (Y + h • basisVec i)) t -
        cellSourceSlice (coordinateSourceWord f w Y) t) -
          cellSourceSlice (coordinateSourceWord f (i :: w) Y) t‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  let q := Q.wordJet w.length 2 hw (coordinateWordDirections w) (coordinateWordDirections_norm w)
  have he : coordinateSourceWord f (i :: w) Y = fun t z =>
      fderiv ℝ (fun X => coordinateSourceWord f w X t z) Y (basisVec i) := by
    funext t z
    exact coordinate_source_word_cons Q i w (by omega) Y t z
  rw [he]
  exact ⟨fun h => independent_source_slice_window_quotient_memLp q (by norm_num) a b Y (basisVec i) h,
    independent_source_slice_window_quotient_energy_tendsto_zero q (by norm_num) hab Y (basisVec i)⟩
end

/-! Differentiated metrics and their quotient remainders act on the actual energy slices. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem parameter_metric_directional_flux_memLp
    (G : ℝ → A → Matrix (Fin 2) (Fin 2) ℝ)
    (hr : ∀ t i j, ContDiff ℝ 1 (fun X => G t X i j))
    (hm : ∀ X i j, Measurable (fun t => G t X i j))
    (C : ℝ) (hb : ∀ t i j X, ‖fderiv ℝ (fun Y => G t Y i j) X‖ ≤ C)
    {a b : ℝ} (Y v : A) (u : ℝ → TorusHk 1 ℂ)
    (hu : MemLp u 2 (volume.restrict (Icc a b))) (k : Fin 2) :
    MemLp (fun t => molecularMetricHilbertFlux
      (Matrix.of (fun i j => fderiv ℝ (fun X => G t X i j) Y v)) (u t) k)
      2 (volume.restrict (Icc a b)) := by
  apply molecularMetricHilbertFlux_memLp _ _ (C * ‖v‖)
    (parameter_metric_directional_measurable G hr hm Y v) _ u hu k
  intro t i j
  simpa only [Matrix.of_apply, Real.norm_eq_abs] using
    ((fderiv ℝ (fun X => G t X i j) Y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb t i j Y) (norm_nonneg v))

omit [NormedAddCommGroup A] [NormedSpace ℝ A] in
theorem parameter_metric_difference_flux_memLp
    (G : ℝ → A → Matrix (Fin 2) (Fin 2) ℝ)
    (hm : ∀ X i j, Measurable (fun t => G t X i j))
    (C : ℝ) (hb : ∀ t X i j, |G t X i j| ≤ C)
    {a b : ℝ} (Y X : A) (u : ℝ → TorusHk 1 ℂ)
    (hu : MemLp u 2 (volume.restrict (Icc a b))) (k : Fin 2) :
    MemLp (fun t => molecularMetricHilbertFlux (G t X - G t Y) (u t) k)
      2 (volume.restrict (Icc a b)) :=
  molecularMetricHilbertFlux_memLp _ _ (C + C)
    (fun i j => (hm X i j).sub (hm Y i j))
    (fun t i j => (abs_sub _ _).trans (add_le_add (hb t X i j) (hb t Y i j))) u hu k

theorem parameter_metric_quotient_flux_memLp
    (G : ℝ → A → Matrix (Fin 2) (Fin 2) ℝ)
    (hr : ∀ t i j, ContDiff ℝ 1 (fun X => G t X i j))
    (hm : ∀ X i j, Measurable (fun t => G t X i j))
    (C₀ C₁ : ℝ) (hb : ∀ t X i j, |G t X i j| ≤ C₀)
    (hd : ∀ t i j X, ‖fderiv ℝ (fun Y => G t Y i j) X‖ ≤ C₁)
    {a b : ℝ} (Y v : A) (h : ℝ) (u : ℝ → TorusHk 1 ℂ)
    (hu : MemLp u 2 (volume.restrict (Icc a b))) (k : Fin 2) :
    MemLp (fun t => molecularMetricHilbertFlux
      (h⁻¹ • (G t (Y + h • v) - G t Y) -
        Matrix.of (fun i j => fderiv ℝ (fun X => G t X i j) Y v)) (u t) k)
      2 (volume.restrict (Icc a b)) := by
  have hs := (parameter_metric_difference_flux_memLp G hm C₀ hb Y (Y + h • v) u hu k).const_smul h⁻¹
  have ht := parameter_metric_directional_flux_memLp G hr hm C₁ hd Y v u hu k
  have he (t : ℝ) : molecularMetricHilbertFlux
      (h⁻¹ • (G t (Y + h • v) - G t Y) -
        Matrix.of (fun i j => fderiv ℝ (fun X => G t X i j) Y v)) (u t) k =
      h⁻¹ • molecularMetricHilbertFlux (G t (Y + h • v) - G t Y) (u t) k -
        molecularMetricHilbertFlux (Matrix.of (fun i j => fderiv ℝ (fun X => G t X i j) Y v)) (u t) k := by
    simp only [molecularMetricHilbertFlux, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, sub_smul, mul_smul, Fin.sum_univ_two, smul_add, smul_sub]
    abel
  simpa only [he, Pi.smul_apply, Pi.sub_apply] using! hs.sub ht
end

/-! Parallel source invariance proves the exact slot-transversality clause of the actual successor. -/

section
open Homogenization AVRegularity.Sobolev

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

variable (G : GenStage D ScalarH Dm b j₀) (P : ProvParams)
    (ht : G.HasTags P) (Mn : WeakMenu) (Din H : ℕ) (hDin : 1 ≤ Din) (hDm : Mn.N + Din ≤ Dm)
    (hpath : ∀ h, StagePath G h → h ≤ H) (rW : ℝ) (hrW : 0 < rW)
    (heps : ∀ i, 0 < D.eps i) (hi : 1 ≤ G.level - 1) (hj : j₀ ≤ G.level - 1)
    (hτ : 0 < ocTau D.α D.q D.Λ (G.level - 1))
    (Cc : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hperiodic : ∀ (p : OddSlot) (c : StageCtx D b j₀ (G.level - 1) p)
      (s : WeakSource G), s.Valid Mn.N Mn.R Din → ∀ d I t X,
      AVenhance.IsZ2Periodic (weakSourceTransferredFlux G Mn.η0 Cc Cc0 p c s d I t X))

local notation "Gsucc" => weakSuccessorStageOfPeriodicTransfer G P ht Mn Din H hDin hDm
  hpath rW hrW heps hi hj hτ Cc Cc0 hperiodic
end

/-! Primitive metric derivative bounds give finite-window flux continuity without normalized upper ellipticity. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem parameter_metric_window_difference_flux_energy_tendsto_zero
    (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ)
    (hr : ∀ t i j, ContDiff ℝ 1 (fun X => G t X i j))
    (hm : ∀ X i j, Measurable (fun t => G t X i j))
    (C : ℝ) (hD : ∀ t i j X, ‖fderiv ℝ (fun Y => G t Y i j) X‖ ≤ C)
    {a b : ℝ} (hab : a ≤ b) (Y : P)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 (volume.restrict (Icc a b))) (k : Fin 2) :
    Tendsto (fun X => ∫ t in a..b,
      ‖molecularMetricHilbertFlux (G t X - G t Y) (u t) k‖ ^ 2) (𝓝 Y) (𝓝 0) := by
  let M := fun X t => G t X - G t Y
  let δ := fun X => C * ‖X - Y‖
  have hM (X : P) (i j : Fin 2) : Measurable (fun t => M X t i j) :=
    (hm X i j).sub (hm Y i j)
  have hb (X : P) (t : ℝ) (i j : Fin 2) : |M X t i j| ≤ δ X := by
    exact independent_parameter_lipschitz (fun Z => G t Z i j)
      (hr t i j) C (hD t i j) Y X
  have hd : Tendsto δ (𝓝 Y) (𝓝 0) := by
    have hh : Continuous δ := by dsimp only [δ]; fun_prop
    simpa only [δ, sub_self, norm_zero, mul_zero] using hh.tendsto Y
  exact molecularMetricHilbertFlux_component_integral_tendsto_zero
    (𝓝 Y) hab M δ hM hb u hu hd k
end

/-! Genuine metric Taylor bounds and lower-state derivatives produce the window product rule. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem parameter_metric_window_product_energy_tendsto_zero
    (G : ℝ → A → Matrix (Fin 2) (Fin 2) ℝ)
    (hr : ∀ t i j, ContDiff ℝ 2 (fun X => G t X i j))
    (hm : ∀ X i j, Measurable (fun t => G t X i j))
    (C₀ C₁ C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hG : ∀ t X i j, |G t X i j| ≤ C₀)
    (hD : ∀ t i j X, ‖fderiv ℝ (fun Y => G t Y i j) X‖ ≤ C₁)
    (hDD : ∀ t i j X, ‖fderiv ℝ (fderiv ℝ (fun Y => G t Y i j)) X‖ ≤ C₂)
    {a b : ℝ} (hab : a ≤ b) (Y v : A)
    (u : A → ℝ → TorusHk 1 ℂ) (du : ℝ → TorusHk 1 ℂ)
    (hu : ∀ X, MemLp (u X) 2 (volume.restrict (Icc a b)))
    (hdu : MemLp du 2 (volume.restrict (Icc a b)))
    (hq : Tendsto (fun h : ℝ => ∫ t in a..b, ∑ j,
      ‖cellDerivativeCLM j (h⁻¹ • (u (Y + h • v) t - u Y t) - du t)‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0)) (k : Fin 2) :
    Tendsto (fun h : ℝ => ∫ t in a..b,
      ‖h⁻¹ • (molecularMetricHilbertFlux (G t (Y + h • v)) (u (Y + h • v) t) k -
          molecularMetricHilbertFlux (G t Y) (u Y t) k) -
        (molecularMetricHilbertFlux
          (Matrix.of (fun i j => fderiv ℝ (fun X => G t X i j) Y v)) (u Y t) k +
          molecularMetricHilbertFlux (G t Y) (du t) k)‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  let X := fun h : ℝ => Y + h • v
  let E := fun h t => h⁻¹ • (u (X h) t - u Y t) - du t
  let D := fun t => Matrix.of (fun i j => fderiv ℝ (fun Z => G t Z i j) Y v)
  have hE h : MemLp (E h) 2 (volume.restrict (Icc a b)) :=
    (((hu (X h)).sub (hu Y)).const_smul h⁻¹).sub hdu
  have hr1 (t : ℝ) (i j : Fin 2) : ContDiff ℝ 1 (fun Z => G t Z i j) :=
    (hr t i j).of_le (by norm_num)
  have hm1 h := parameter_metric_quotient_flux_memLp G hr1 hm C₀ C₁ hG hD Y v h
    (u Y) (hu Y) k
  have hm2 h := molecularMetricHilbertFlux_memLp _ (fun t => G t (X h)) C₀
    (hm (X h)) (fun t => hG t (X h)) (E h) (hE h) k
  have hm3 h := parameter_metric_difference_flux_memLp G hm C₀ hG Y (X h) du hdu k
  have ht1 := parameter_metric_window_quotient_flux_energy_tendsto_zero G hr hm C₂ hC₂
    hDD hab Y v (u Y) (hu Y) k
  have ht2 := molecularMetricHilbertFlux_state_integral_tendsto_zero (𝓝[≠] 0) hab
    (fun h t => G t (X h)) C₀ (fun h => hm (X h)) (fun h t => hG t (X h)) E hE hq k
  have hX : Tendsto X (𝓝[≠] 0) (𝓝 Y) := by
    have hc : Continuous X := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [X, zero_smul, add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have ht3 := (parameter_metric_window_difference_flux_energy_tendsto_zero G hr1 hm C₁ hD
    hab Y du hdu k).comp hX
  have ht12 := window_normSq_add_integral_tendsto_zero (𝓝[≠] 0) hab _ _ hm1 hm2 ht1 ht2
  have ht123 := window_normSq_add_integral_tendsto_zero (𝓝[≠] 0) hab _ _
    (fun h => (hm1 h).add (hm2 h)) hm3 ht12 ht3
  simpa only [molecularMetricHilbertFlux_product_residual, X, E, D, Pi.add_apply] using ht123
end

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.WeakEntryProofs

/-! Higher source reserves produce actual bounded window carriers without a small-drift premise. -/

open AVRegularity.EntryWeakProofs

def higherSourceWindowTraceBound (a b : ℝ) (K : ℕ) (Cv Ns Nf : ℝ) : ℝ :=
  Real.sqrt ((higherSourceWindowBudget a b K Ns Nf * Real.exp ((1 + 4 *
    (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ^ 2) * (b - a))) / factorialWeightMin 1 K)

theorem higher_source_window_zero_production {a b : ℝ} (hab : a < b)
    {P : MolecularData} {K : ℕ} {src : ℝ → Vec 2 → ℂ}
    {flux : ℝ → Vec 2 → ComplexCellVector}
    (Q : HigherSourceCarrierData (Icc a b) K src flux)
    (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (dataCoefficients P) src flux D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ,
      torusHkValueCLM w = cellRawTrace D t ∧
        ‖w‖ ≤ higherSourceWindowTraceBound a b K Cv Q.Ns Q.Nf := by
  have hz : factorialNormSq 1 (0 : TorusHk K ℂ).val = 0 := by
    simp [factorialNormSq, derivativeNormSq]
  have hbudget : factorialNormSq 1 (0 : TorusHk K ℂ).val +
      (∫ s in a..b, factorialNormSq 1 (Q.S s).val + 4 * factorialNormSq 1 (Q.F s).val) ≤
      higherSourceWindowBudget a b K Q.Ns Q.Nf := by
    rw [hz, zero_add]
    exact higher_source_window_budget hab.le Q
  exact molecular_actual_flux_higher_window_carrier_bound (initial := 0) hab
    Q.scalar_memLp Q.flux_memLp K Cv hCv hv hp hb
    Q.S Q.scalar_value Q.F Q.scalar_carrier_memLp Q.flux_carrier_memLp Q.flux_value
    0 (by simp only [map_zero]) _ (higherSourceWindowBudget_nonneg hab.le K Q.Ns Q.Nf)
    hbudget D hD (hi.trans (by
      simpa only using! (Lp.coeFn_zero ℂ 2
        (volume.restrict AVenhance.unitCube)).symm))

theorem higher_source_window_carrier_exists {a b : ℝ} (hab : a < b)
    {P : MolecularData} {K : ℕ} {src : ℝ → Vec 2 → ℂ}
    {flux : ℝ → Vec 2 → ComplexCellVector}
    (Q : HigherSourceCarrierData (Icc a b) K src flux)
    (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (dataCoefficients P) src flux D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∃ w : ℝ → TorusHk K ℂ, StronglyMeasurable w ∧
      (∀ t, ‖w t‖ ≤ higherSourceWindowTraceBound a b K Cv Q.Ns Q.Nf) ∧
      ∀ t ∈ Icc a b, torusHkValueCLM (w t) =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue D t := by
  exact rawHigherWindowCarrier_exists hab.le D hD K _ (Real.sqrt_nonneg _)
    (higher_source_window_zero_production hab Q Cv hCv hv hp hb D hD hi)

end AVRegularity.WeakEntryProofs
end

section
namespace AVRegularity.WeakEntryProofs

/-! Shared scalar and flux budgets give a shared finite-window trace bound. -/

section
open AVRegularity.Sobolev AVRegularity.EntryWeakProofs AVRegularity.CoupledEnergy.Variational

theorem higherSourceWindowTraceBound_mono {a b : ℝ} (hab : a ≤ b)
    (K : ℕ) (Cv : ℝ) {Ns Nf Rs Rf : ℝ}
    (hs : 0 ≤ Ns) (hf : 0 ≤ Nf) (hNs : Ns ≤ Rs) (hNf : Nf ≤ Rf) :
    higherSourceWindowTraceBound a b K Cv Ns Nf ≤
      higherSourceWindowTraceBound a b K Cv Rs Rf := by
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (factorialWeightMin_pos 1 (by norm_num) (K := K)).le
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
  apply mul_le_mul_of_nonneg_left _ (factorialWeightMax_nonneg_local K)
  exact add_le_add (pow_le_pow_left₀ hs hNs 2)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf hNf 2) (by norm_num))
end

/-! Actual lower-word derivatives produce the full differentiated ordered-word flux. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {d : ℕ}

theorem molecularWordHilbertFlux_directional_integral_tendsto_zero {a b : ℝ} (hab : a ≤ b)
    (G : List (Fin d) → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (u : List (Fin d) → Vec d → ℝ → TorusHk 1 ℂ)
    (w : List (Fin d)) (Y : Vec d) (i : Fin d)
    (C₀ C₁ C₂ : List (Fin d) → ℝ)
    (hC₂ : ∀ p ∈ independentWordForcing w, 0 ≤ C₂ p.1)
    (hr : ∀ p ∈ independentWordForcing w, ∀ t j k,
      ContDiff ℝ 2 (fun X => G p.1 t X j k))
    (hm : ∀ p ∈ independentWordForcing w, ∀ X j k,
      Measurable (fun t => G p.1 t X j k))
    (hb : ∀ p ∈ independentWordForcing w, ∀ t X j k, |G p.1 t X j k| ≤ C₀ p.1)
    (hD : ∀ p ∈ independentWordForcing w, ∀ t j k X,
      ‖fderiv ℝ (fun Z => G p.1 t Z j k) X‖ ≤ C₁ p.1)
    (hDD : ∀ p ∈ independentWordForcing w, ∀ t j k X,
      ‖fderiv ℝ (fderiv ℝ (fun Z => G p.1 t Z j k)) X‖ ≤ C₂ p.1)
    (hcons : ∀ p ∈ independentWordForcing w, ∀ t,
      G (i :: p.1) t Y = Matrix.of
        (fun j k => fderiv ℝ (fun X => G p.1 t X j k) Y (basisVec i)))
    (hu : ∀ p ∈ independentWordForcing w, ∀ X,
      MemLp (u p.2 X) 2 (volume.restrict (Icc a b)))
    (hdu : ∀ p ∈ independentWordForcing w,
      MemLp (u (i :: p.2) Y) 2 (volume.restrict (Icc a b)))
    (hq : ∀ p ∈ independentWordForcing w,
      Tendsto (fun h : ℝ => ∫ t in a..b, ∑ j,
        ‖cellDerivativeCLM j (h⁻¹ • (u p.2 (Y + h • basisVec i) t - u p.2 Y t) -
          u (i :: p.2) Y t)‖ ^ 2) (𝓝[≠] 0) (𝓝 0)) (k : Fin 2) :
    Tendsto (fun h : ℝ => ∫ t in a..b,
      ‖h⁻¹ • (molecularWordHilbertFlux (fun p t => G p t (Y + h • basisVec i))
          (fun p => u p (Y + h • basisVec i)) w t k -
        molecularWordHilbertFlux (fun p t => G p t Y) (fun p => u p Y) w t k) -
        molecularWordHilbertFluxDerivative (fun p t => G p t Y) (fun p => u p Y) i w t k‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
  let X := fun h : ℝ => Y + h • basisVec i
  let f := fun (p : List (Fin d) × List (Fin d)) h t =>
    h⁻¹ • (molecularMetricHilbertFlux (G p.1 t (X h)) (u p.2 (X h) t) k -
      molecularMetricHilbertFlux (G p.1 t Y) (u p.2 Y t) k) -
      (molecularMetricHilbertFlux (G (i :: p.1) t Y) (u p.2 Y t) k +
        molecularMetricHilbertFlux (G p.1 t Y) (u (i :: p.2) Y t) k)
  have hmem p (hp : p ∈ independentWordForcing w) h :
      MemLp (f p h) 2 (volume.restrict (Icc a b)) := by
    have hreg t j k : ContDiff ℝ 1 (fun Z => G p.1 t Z j k) :=
      (hr p hp t j k).of_le (by norm_num)
    have hmG j k := parameter_metric_directional_measurable (G p.1) hreg
      (hm p hp) Y (basisVec i) j k
    have hbD t j k : |G (i :: p.1) t Y j k| ≤ C₁ p.1 * ‖basisVec i‖ := by
      rw [hcons p hp t]
      change |fderiv ℝ (fun X => G p.1 t X j k) Y (basisVec i)| ≤ _
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ (fun X => G p.1 t X j k) Y).le_opNorm (basisVec i)).trans
        (mul_le_mul_of_nonneg_right (hD p hp t j k Y) (norm_nonneg _))
    have hmD j k : Measurable (fun t => G (i :: p.1) t Y j k) := by
      simpa only [hcons p hp, Matrix.of_apply] using hmG j k
    exact (((molecularMetricHilbertFlux_memLp _ (fun t => G p.1 t (X h)) (C₀ p.1)
      (hm p hp (X h)) (fun t => hb p hp t (X h)) (u p.2 (X h)) (hu p hp (X h)) k).sub
      (molecularMetricHilbertFlux_memLp _ (fun t => G p.1 t Y) (C₀ p.1)
        (hm p hp Y) (fun t => hb p hp t Y) (u p.2 Y) (hu p hp Y) k)).const_smul h⁻¹).sub
      ((molecularMetricHilbertFlux_memLp _ (fun t => G (i :: p.1) t Y)
        (C₁ p.1 * ‖basisVec i‖) hmD hbD (u p.2 Y) (hu p hp Y) k).add
        (molecularMetricHilbertFlux_memLp _ (fun t => G p.1 t Y) (C₀ p.1)
          (hm p hp Y) (fun t => hb p hp t Y) (u (i :: p.2) Y) (hdu p hp) k))
  have ht p (hp : p ∈ independentWordForcing w) :
      Tendsto (fun h => ∫ t in a..b, ‖f p h t‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [f, X, hcons p hp] using
      parameter_metric_window_product_energy_tendsto_zero (G p.1) (hr p hp) (hm p hp)
        (C₀ p.1) (C₁ p.1) (C₂ p.1) (hC₂ p hp) (hb p hp) (hD p hp) (hDD p hp)
        hab Y (basisVec i) (u p.2) (u (i :: p.2) Y) (hu p hp) (hdu p hp) (hq p hp) k
  have hall := window_normSq_list_sum_integral_tendsto_zero (𝓝[≠] 0) hab
    (independentWordForcing w) f hmem ht
  simpa only [molecularWordHilbertFlux, molecularWordHilbertFluxDerivative,
    window_list_sum_apply, List.map_map, Function.comp_def, window_list_sum_quotient,
    f, X, Pi.add_apply] using hall
end

/-! Genuine primitive coordinate jets produce the coherent family of Hilbert word equations. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open scoped ContDiff
variable {d H : ℕ}

def coordinateWordHilbertSource (f : ℝ → Vec 2 → Vec d → ℂ)
    (w : List (Fin d)) (Y : Vec d) : ℝ → ComplexCellL2 :=
  cellSourceSlice (coordinateSourceWord f w Y)
end

/-! Native localized lift uniqueness holds on arbitrary histories, without quantitative metric bounds. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, InnerProductSpace ℝ (hv i)]
  [∀ i, FiniteDimensional ℝ (hv i)] {Dm : ℕ}

theorem native_family_lift_coefficients_unique (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hslot : Odd slot) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm hv) (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (a b : ℝ) (hab : a ≤ b) (N H sX sZ sX' sZ' : ℕ)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι hv)
    (hc : IsLiftSequenceOn Ω (familyLiftData D m slot A ρ edge) sX sZ a b N H Cc)
    (hd : IsLiftSequenceOn Ω (familyLiftData D m slot A ρ edge) sX' sZ' a b N H Dc) :
    ∀ hh, hh ≤ H → ∀ n l (α : DerivativeWord2 l) t, t ∈ Set.Icc a b →
      ∀ X ∈ Ω, ∀ z v u, Cc hh n l α t X z v u = Dc hh n l α t X z v u := by
  let Q := familyLiftData D m slot A ρ edge
  apply localLift_coefficients_unique_of_window_data Ω hΩ Q a b hab N H sX sZ sX' sZ' _ Cc Dc hc hd
  intro X _
  obtain ⟨lo, hi, hlo, he⟩ := Providers.GenSem.familyLiftData_pos_window D hζ m slot A ρ edge a b X
  obtain ⟨Mv, hMv⟩ := Providers.GenSem.familyLiftData_v_bounded D hζ m hslot A ρ edge
  exact ⟨lo, hi, Mv, Uniqueness.windowData_of_elliptic
    (fun t => Matrix.of (Q.G t X)) Q.v a b lo hi Mv
    (fun t => Providers.GenSem.familyLiftData_symm D m slot A ρ edge t X 0 1)
    hlo he (fun t _ z => hMv t z)⟩
end

end AVRegularity.WeakEntryProofs
end
