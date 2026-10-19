-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeakAssembly.WindowListL2Representative
public import AVRegularity.EntryWeakAssembly.RootBirthLaw
import AVRegularity.EntryWeakAssembly.WindowFieldExtension
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
public import AVRegularity.CycleComparison.Lift.DiagonalMeanLeftTermsActionOfCoefficients
import AVRegularity.EntryWeakAssembly.MeanLeftTermsLocalCongruence
public import AVRegularity.EntryWeak.NormalizedLiftAComponentDecomposition
public import AVRegularity.Construction.Preservation.Ledger.ActualSourceSums
import AVRegularity.Construction.InitialLayer.Comparison
import AVRegularity.EntryWeakAssembly.MassRecursion
import Mathlib.Algebra.Ring.IsFormallyReal

section
section
/-! The actual weak construction has a fixed graph depth. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

open EntryWeakProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakConstruction_depth (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (stage : ℕ → GenStage D hr Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage)
    (i : ℕ) (hi : M ≤ i) (hit : i ≤ M + J) :
    (stage i).fam.HasDepthAtMost (J * Mn.R) := by
  obtain ⟨hb, he⟩ := weakConstruction_rank_bounds P Mn M J r rW stage hc i hi hit
  apply family_hasDepthAtMost_of_rank (stage i).fam (fun v => weakComponentRank v.1)
    (J * Mn.R) _ he
  intro v
  exact (hb v.1 v.2).trans (Nat.mul_le_mul_right Mn.R (by omega))

end AVRegularity.WeakEntryProofs
end
end

section
/-! Actual Hilbert word derivatives and finite higher quotients give joint fast and slow regularity. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
variable {d : ℕ}

theorem higher_trace_word_classical_joint_contDiff (N K : ℕ)
    (u : List (Fin d) → Vec d → ComplexCellL2)
    (w : List (Fin d) → Vec d → TorusHk K ℂ)
    (hw : ∀ p, p.length ≤ N → ∀ Y, torusHkValueCLM (w p Y) = u p Y)
    (hc : ∀ p, p.length ≤ N → Continuous (u p))
    (hd : ∀ p, p.length < N → ∀ Y i,
      Tendsto (fun h : ℝ => h⁻¹ • (u p (Y + h • basisVec i) - u p Y) - u (i :: p) Y)
        (𝓝[≠] 0) (𝓝 0))
    (R : List (Fin d) → ℝ) (hb : ∀ p, p.length ≤ N → ∀ Y, ‖w p Y‖ ≤ R p)
    (hq : ∀ p, p.length < N → ∀ i : Fin d, ∃ B : ℝ, ∀ Y (h : ℝ), h ≠ 0 →
      ∃ q : TorusHk K ℂ,
        torusHkValueCLM q = h⁻¹ • (u p (Y + h • basisVec i) - u p Y) ∧ ‖q‖ ≤ B) :
    ∀ p r n, p.length + r ≤ N → n + r + 4 ≤ K →
      ContDiff ℝ (r : ℕ∞) (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n
        (realClassicalLift K (mapTorusHk Complex.reCLM (w p X.1))) X.2) := by
  intro p r n hpr hn
  apply coordinate_word_joint_contDiff d N (K - 4)
    (fun p Y => realClassicalLift K (mapTorusHk Complex.reCLM (w p Y)))
    _ _ _ p r n hpr (by omega)
  · intro p hp n hn
    apply joint_continuous_of_uniform_slice_variation
      (fun Y z => iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM (w p Y))) z)
      (fun z => molecular_higher_trace_fast_jet_continuous K n (by omega) (w p) (u p)
        (hc p hp) (hw p hp) (R p) (hb p hp) z)
      (cellClassicalSobolevConstant K (n + 1) * R p)
    intro Y z x
    exact (realHigherCarrier_fast_jet_lipschitz K n (by omega) (w p Y) z x).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb p hp Y) (cellClassicalSobolevConstant_nonneg K (n + 1)))
        (norm_nonneg _))
  · intro p _ Y
    exact realClassicalLift_contDiff K (K - 4) (by omega) _
  · intro p hp n hn i Y z
    obtain ⟨B, hB⟩ := hq p hp i
    have hpi : (i :: p).length ≤ N := by simp only [List.length_cons]; omega
    apply molecular_higher_trace_jet_hasDerivAt K n (by omega)
      (fun h => w p (Y + h • basisVec i)) (w (i :: p) Y)
      (fun h => u p (Y + h • basisVec i)) (u (i :: p) Y)
      (fun h => hw p (by omega) _) (hw (i :: p) hpi Y)
    · simpa only [zero_smul, add_zero] using hd p hp Y i
    · filter_upwards [self_mem_nhdsWithin] with h hh
      obtain ⟨q, hq, hqb⟩ := hB Y h hh
      have he : h⁻¹ • (w p (Y + h • basisVec i) - w p Y) = q := by
        apply TorusHk.ext_value
        change torusHkValueCLM (h⁻¹ • (w p (Y + h • basisVec i) - w p Y)) = torusHkValueCLM q
        rw [map_smul, map_sub, hw p (by omega), hw p (by omega)]
        exact hq.symm
      simpa only [zero_smul, add_zero, he] using hqb


end AVRegularity.WeakEntryProofs
end
end

section
/-! Uniform mass allocation for all finite weak response menus. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

theorem weakAlphabet_mass_factor (N J : ℕ) (hN : 1 ≤ N) (hJ : 1 ≤ J) :
    (N : ℝ) * weakCw N J = 1 / (4 * (J : ℝ)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hj : (J : ℝ) ≠ 0 := by exact_mod_cast (by omega : J ≠ 0)
  simp only [weakCw, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

 theorem weakExtComps_mass_geometric_bound (D : OCData) (N J m R : ℕ) (η : ℝ)
    (hN : 1 ≤ N) (hJ : 1 ≤ J) (hη : 0 ≤ η)
    (heps : ∀ i, 0 ≤ D.eps i ∧ D.eps i ≤ 1) (S : Finset Comp) :
    ∑ v ∈ weakExtComps m N R S, weakMass D N J η v ≤
      (∑ v ∈ S, weakMass D N J η v) / (1 - 1 / (4 * (J : ℝ))) := by
  let r := weakCw N J * D.eps (m - 1) ^ (η / 2)
  let x := (N : ℝ) * r
  have hj : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have ht0 : 0 < 1 / (4 * (J : ℝ)) := by positivity
  have ht1 : 1 / (4 * (J : ℝ)) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith only [hj]
  have he := Real.rpow_le_one (z := η / 2) (heps (m - 1)).1 (heps (m - 1)).2
    (div_nonneg hη (by norm_num))
  have hx : x ≤ 1 / (4 * (J : ℝ)) := by
    dsimp [x, r]
    rw [← mul_assoc, weakAlphabet_mass_factor N J hN hJ]
    exact (mul_le_mul_of_nonneg_left he ht0.le).trans_eq (mul_one _)
  have hx0 : 0 ≤ x := by
    dsimp [x, r]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply mul_nonneg
    · unfold weakCw
      positivity
    · exact Real.rpow_nonneg (heps (m - 1)).1 _
  have hs := weakExtComps_mass_sum_le D N J m R η (fun i => (heps i).1) S
  have hg := one_add_geometric_Icc_le x hx0 (hx.trans_lt ht1) R
  have hd := one_div_le_one_div_of_le (sub_pos.mpr ht1) (sub_le_sub_left hx 1)
  have hf : 0 ≤ ∑ v ∈ S, weakMass D N J η v :=
    Finset.sum_nonneg (fun v _ => weakMass_nonneg D N J η (fun i => (heps i).1) v)
  simp_rw [← mul_pow] at hs
  exact hs.trans ((mul_le_mul_of_nonneg_left (hg.trans hd) hf).trans_eq
    (by simp only [div_eq_mul_inv, one_mul]))

end AVRegularity.WeakEntryProofs
end
end

section
/-! The literal weak tags give positive constituent records and the required degree bounds. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakSource_tag_size_nonneg (G : GenStage D hr Dm b j₀) (P : ProvParams)
    (ht : G.HasTags P) (m : ℕ) (rW η : ℝ) (heps : 0 < D.eps (m - 1)) (s : WeakSource G) :
    0 ≤ (s.weakTag P m rW η).size := by
  cases s with
  | inherited w h π n => exact EntryWeakProofs.stagePath_stored_witness_nonneg G P ht π
  | eddy v w n =>
      exact mul_nonneg (Real.rpow_nonneg heps.le _) (sq_nonneg _)

def weakSourceRecord (G : GenStage D hr Dm b j₀) (P : ProvParams) (ht : G.HasTags P)
    (m : ℕ) (rW η : ℝ) (heps : ∀ i, 0 < D.eps i) (hrW : 0 < rW)
    (s : WeakSource G) : ConstituentRecord where
  size := (s.weakTag P m rW η).size
  size_nonneg := weakSource_tag_size_nonneg G P ht m rW η (heps _) s
  birthLevel := (s.weakTag P m rW η).birthLevel
  birthExcess := (s.weakTag P m rW η).birthExcess
  length := D.eps m
  length_pos := heps m
  width := rW
  width_pos := hrW
  births := (s.weakTag P m rW η).births

theorem weakSourceRecord_matches (G : GenStage D hr Dm b j₀) (P : ProvParams)
    (ht : G.HasTags P) (m : ℕ) (rW η : ℝ) (heps : ∀ i, 0 < D.eps i)
    (hrW : 0 < rW) (s : WeakSource G) (idx : ℕ) :
    ((Prov.seed idx (s.weakTag P m rW η)).tags P).Matches
      (weakSourceRecord G P ht m rW η heps hrW s) := by
  cases s <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem weakSource_degree_bounds (G : GenStage D hr Dm b j₀) (N R Din : ℕ)
    (hDin : 1 ≤ Din) (s : WeakSource G) (hs : s.Valid N R Din) :
    2 ≤ s.degree ∧ s.degree ≤ N + Din := by
  cases s with
  | inherited w h π n => exact ⟨hs.2.2.1, hs.2.2.2⟩
  | eddy v w n => exact ⟨hs.2.2.1, hs.2.2.2.trans (by omega)⟩

end AVRegularity.WeakEntryProofs
end
end

section
/-! The actual finite-window quotient equation needs no all-time inverse witness. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleEvolution

theorem cell_window_metric_quotient_solution (I : Set ℝ)
    (G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hG : ∀ t z, (G t z).IsSymm) (hH : ∀ t z, (H t z).IsSymm)
    (f g : ℝ → Vec 2 → ℂ) (F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D E : ℝ → RawJet2 1 ℂ) (r : ℝ)
    (hD : IsCellSolution I ⟨G, v, 0, 0⟩ f F D)
    (hE : IsCellSolution I ⟨H, v, 0, 0⟩ g F' E) :
    IsCellSolution I ⟨G, v, 0, 0⟩ (r • (g - f))
      (r • (F' - F) + cellMetricFlux (r • (H - G)) E) (r • (E - D)) := by
  have hc := cellSolution_metric_change I G H v g F' E hG hH hE
  have hd := cellSolution_add hc (cellSolution_smul hD (-1))
  have hs : g + (-1 : ℝ) • f = g - f := by simp only [neg_one_smul, sub_eq_add_neg]
  have hu : E + (-1 : ℝ) • D = E - D := by simp only [neg_one_smul, sub_eq_add_neg]
  have hf : F' + cellMetricFlux (H - G) E + (-1 : ℝ) • F =
      (F' - F) + cellMetricFlux (H - G) E := by rw [neg_one_smul]; abel
  rw [hs, hu, hf] at hd
  have hq := cellSolution_smul hd r
  rw [smul_add, ← cellMetricFlux_smul_metric] at hq
  exact hq

end AVRegularity.WeakEntryProofs
end
end

section
/-! The complete actual weak construction has total mass at most two thirds. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakConstruction_mass_sum_le (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (stage : ℕ → GenStage D hr Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage)
    (hN : 1 ≤ Mn.N) (hJ : 1 ≤ J) (hη : 0 ≤ Mn.η0)
    (heps : ∀ i, 0 ≤ D.eps i ∧ D.eps i ≤ 1) :
    ∑ v ∈ (stage M).comps, weakMass D Mn.N J Mn.η0 v ≤ 2 / 3 := by
  classical
  let c : ℝ := 1 / (1 - 1 / (4 * (J : ℝ)))
  have hj : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have ht : 1 / (4 * (J : ℝ)) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith only [hj]
  have hc0 : 0 ≤ c := div_nonneg (by norm_num) (sub_pos.mpr ht).le
  have main : ∀ n, n ≤ J →
      (∑ v ∈ (stage (M + J - n)).comps, weakMass D Mn.N J Mn.η0 v) ≤
        (1 / 2 : ℝ) * c ^ n := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [Nat.sub_zero, hc.2.1.2.1]
        simp only [Finset.sum_singleton, weakMass_root, pow_zero, mul_one, le_refl]
    | succ n ih =>
        intro hn
        have hp := (hc.2.2 (M + J - n) (by omega) (by omega)).1
        have he : M + J - (n + 1) = M + J - n - 1 := by omega
        rw [he, hp.2.2.2.1]
        have hs := weakExtComps_mass_geometric_bound D Mn.N J (stage (M + J - n)).level
          Mn.R Mn.η0 hN hJ hη heps (stage (M + J - n)).comps
        calc
          _ ≤ _ := hs
          _ = (∑ v ∈ (stage (M + J - n)).comps, weakMass D Mn.N J Mn.η0 v) * c := by
            simp only [c, div_eq_mul_inv, one_mul]
          _ ≤ ((1 / 2 : ℝ) * c ^ n) * c :=
            mul_le_mul_of_nonneg_right (ih (by omega)) hc0
          _ = (1 / 2 : ℝ) * c ^ (n + 1) := by rw [pow_succ, mul_assoc]
  have h := main J le_rfl
  rw [Nat.add_sub_cancel] at h
  exact h.trans (weakMass_budget_price J hJ)

end AVRegularity.WeakEntryProofs
end
end

section
/-! Actual Hilbert word derivatives and finite higher quotients give joint fast and slow regularity. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
variable {d : ℕ}

theorem higher_trace_word_classical_joint_bound (N K : ℕ)
    (u : List (Fin d) → Vec d → ComplexCellL2)
    (w : List (Fin d) → Vec d → TorusHk K ℂ)
    (hw : ∀ p, p.length ≤ N → ∀ Y, torusHkValueCLM (w p Y) = u p Y)
    (hc : ∀ p, p.length ≤ N → Continuous (u p))
    (hd : ∀ p, p.length < N → ∀ Y i,
      Tendsto (fun h : ℝ => h⁻¹ • (u p (Y + h • basisVec i) - u p Y) - u (i :: p) Y)
        (𝓝[≠] 0) (𝓝 0))
    (R : List (Fin d) → ℝ) (hb : ∀ p, p.length ≤ N → ∀ Y, ‖w p Y‖ ≤ R p)
    (hq : ∀ p, p.length < N → ∀ i : Fin d, ∃ B : ℝ, ∀ Y (h : ℝ), h ≠ 0 →
      ∃ q : TorusHk K ℂ,
        torusHkValueCLM q = h⁻¹ • (u p (Y + h • basisVec i) - u p Y) ∧ ‖q‖ ≤ B)
    (hK : 4 ≤ K) (S : ℝ) (hS : 0 ≤ S)
    (hRS : ∀ p, p.length ≤ N → R p ≤ S) :
    ∀ p r n, p.length + r ≤ N → n + r + 4 ≤ K →
      ∀ X : Vec d × Vec 2,
        ‖iteratedFDeriv ℝ r (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n
          (realClassicalLift K (mapTorusHk Complex.reCLM (w p X.1))) X.2) X‖ ≤
          ((d : ℝ) + 1) ^ r *
            (∑ m : Fin (K - 4 + 1), cellClassicalSobolevConstant K m.val * S) := by
  let B := ∑ m : Fin (K - 4 + 1), cellClassicalSobolevConstant K m.val * S
  have hB : 0 ≤ B := Finset.sum_nonneg fun m _ =>
    mul_nonneg (cellClassicalSobolevConstant_nonneg K m.val) hS
  have hprice (n : ℕ) (hn : n ≤ K - 4) : cellClassicalSobolevConstant K n * S ≤ B :=
    Finset.single_le_sum (fun m _ => mul_nonneg (cellClassicalSobolevConstant_nonneg K m.val) hS)
      (Finset.mem_univ (⟨n, by omega⟩ : Fin (K - 4 + 1)))
  intro p r n hpr hn X
  apply coordinate_word_joint_derivative_bound d N (K - 4)
    (fun p Y => realClassicalLift K (mapTorusHk Complex.reCLM (w p Y)))
    _ _ _ B hB _ p r n hpr (by omega) X
  · intro p hp n hn
    apply joint_continuous_of_uniform_slice_variation
      (fun Y z => iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM (w p Y))) z)
      (fun z => molecular_higher_trace_fast_jet_continuous K n (by omega) (w p) (u p)
        (hc p hp) (hw p hp) (R p) (hb p hp) z)
      (cellClassicalSobolevConstant K (n + 1) * R p)
    intro Y z x
    exact (realHigherCarrier_fast_jet_lipschitz K n (by omega) (w p Y) z x).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb p hp Y) (cellClassicalSobolevConstant_nonneg K (n + 1)))
        (norm_nonneg _))
  · intro p _ Y
    exact realClassicalLift_contDiff K (K - 4) (by omega) _
  · intro p hp n hn i Y z
    obtain ⟨B, hB⟩ := hq p hp i
    have hpi : (i :: p).length ≤ N := by simp only [List.length_cons]; omega
    apply molecular_higher_trace_jet_hasDerivAt K n (by omega)
      (fun h => w p (Y + h • basisVec i)) (w (i :: p) Y)
      (fun h => u p (Y + h • basisVec i)) (u (i :: p) Y)
      (fun h => hw p (by omega) _) (hw (i :: p) hpi Y)
    · simpa only [zero_smul, add_zero] using hd p hp Y i
    · filter_upwards [self_mem_nhdsWithin] with h hh
      obtain ⟨q, hq, hqb⟩ := hB Y h hh
      have he : h⁻¹ • (w p (Y + h • basisVec i) - w p Y) = q := by
        apply TorusHk.ext_value
        change torusHkValueCLM (h⁻¹ • (w p (Y + h • basisVec i) - w p Y)) = torusHkValueCLM q
        rw [map_smul, map_sub, hw p (by omega), hw p (by omega)]
        exact hq.symm
      simpa only [zero_smul, add_zero, he] using hqb

  · intro p hp n hn Y z
    exact ((realHigherCarrier_derivative_norm_le K n (by omega) (w p Y) z).trans
      (mul_le_mul_of_nonneg_left ((hb p hp Y).trans (hRS p hp))
        (cellClassicalSobolevConstant_nonneg K n))).trans (hprice n hn)


end AVRegularity.WeakEntryProofs
end
end

section
/-! Changing an inverse field outside its solution window preserves the cell-inverse relation
`IsCellFieldInverse`. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

open MeasureTheory Homogenization AVRegularity.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_field_congr_on (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (r : ℕ) (a b : ℝ) (hab : a ≤ b)
    (c₀ : Vec 2 → E) (g c d : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse G v r a b c₀ g c) (he : ∀ t ∈ Set.Icc a b, c t = d t) :
    IsCellFieldInverse G v r a b c₀ g d := by
  refine ⟨fun t ht => he t ht ▸ hc.1 t ht, ?_⟩
  intro l
  have hj (t : ℝ) (ht : t ∈ Set.Icc a b) : cellJetOfField l c t = cellJetOfField l d t := by
    funext α z
    simp only [cellJetOfField, he t ht]
  have hs := AVRegularity.InitialLayer.cellSolution_congr_jet measurableSet_Icc hj (hc.2 l).1
  refine ⟨hs, ?_, ?_, ?_⟩
  · intro t ht
    simpa only [cellValue, hj t ht] using (hc.2 l).2.1 t ht
  · simpa only [cellValue, hj a ⟨le_rfl, hab⟩] using (hc.2 l).2.2.1
  · exact CycleComparison.Lift.cellSolution_compact_energy_finite a b hab _ _ _ _ hs

end AVRegularity.WeakEntryProofs
end
end

section
/-! The weak readout-weighted mass is no larger than the ordinary mass. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

theorem weakReadout_mass_sum_le (D : OCData) (N J : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (heps : ∀ i, 0 ≤ D.eps i ∧ D.eps i ≤ 1) (S : Finset Comp) :
    ∑ v ∈ S, weakReadoutWeight D η v ^ 2 * weakMass D N J η v ≤
      ∑ v ∈ S, weakMass D N J η v := by
  apply Finset.sum_le_sum
  intro v _
  have hw := pow_le_one₀ (weakReadoutWeight_nonneg D η (fun i => (heps i).1) v)
    (weakReadoutWeight_le_one D η hη heps v) (n := 2)
  exact (mul_le_mul_of_nonneg_right hw
    (weakMass_nonneg D N J η (fun i => (heps i).1) v)).trans_eq (one_mul _)

end AVRegularity.WeakEntryProofs
end
end

section
/-! The literal source convolution preserves the local germs of all lift coefficients. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFluxConvolutionLeftTerms_slow_local_edge_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (edge edge' : ConstituentEdges D h)
    (η t : ℝ) (n : ℕ) (c d : ℕ → LiftCoeff ι h) (k : Fin 2) (v : ι)
    (hΓ : SlowOpenEdgeEq Ω t edge edge')
    (he : ∀ q m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ X ∈ Ω, ∀ z u u',
      c q m α t X z u u' = d q m α t X z u u') :
    List.Forall₂ (LeftTermSlowEq Ω) (sourceFluxConvolutionLeftTerms edge η t n c k v)
      (sourceFluxConvolutionLeftTerms edge' η t n d k v) := by
  unfold sourceFluxConvolutionLeftTerms
  apply leftTermSlowEq_flatMap_same
  intro j _
  exact sourceFluxLeftTerms_slow_local_edge_congr hΩ edge edge' η t (n - j)
    (c (n - j)) (d (n - j)) k j v hΓ (he (n - j))

theorem sourceConvolutionLeftTerms_slow_local_edge_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (edge edge' : ConstituentEdges D h)
    (η t : ℝ) (n : ℕ) (c d : ℕ → LiftCoeff ι h) (v : ι)
    (hΓ : SlowOpenEdgeEq Ω t edge edge')
    (he : ∀ q m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ X ∈ Ω, ∀ z u u',
      c q m α t X z u u' = d q m α t X z u u') :
    List.Forall₂ (LeftTermSlowEq Ω) (sourceConvolutionLeftTerms edge η t n c v)
      (sourceConvolutionLeftTerms edge' η t n d v) := by
  unfold sourceConvolutionLeftTerms
  apply leftTermSlowEq_flatMap_same
  intro k _
  apply covariantLeftTermStep_slow_local_congr hΩ η k
  intro q
  exact sourceFluxConvolutionLeftTerms_slow_local_edge_congr Ω hΩ edge edge' η t
    q c d k v hΓ he

end AVRegularity.WeakEntryProofs
end
end

section
/-! The exact full planar triangular difference equation, including all metric perturbation terms. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.WeakEntryProofs
open AVRegularity.EntryWeakProofs
variable {I : Type*}

theorem independent_word_window_difference_solution (J : Set ℝ)
    (G H : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (f g : List I → ℝ → Vec 2 → ℂ)
    (F F' : List I → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D E : List I → ℝ → RawJet2 1 ℂ) (α : List I) (r : ℝ)
    (hGsym : ∀ t x, (G [] t x).IsSymm) (hHsym : ∀ t x, (H [] t x).IsSymm)
    (hD : IsCellSolution J ⟨G [], v, 0, 0⟩ (f α)
      (F α + independentWordMetricFlux G D α) (D α))
    (hE : IsCellSolution J ⟨H [], v, 0, 0⟩ (g α)
      (F' α + independentWordMetricFlux H E α) (E α)) :
    IsCellSolution J ⟨G [], v, 0, 0⟩ (r • (g α - f α))
      (((r • (F' α - F α) + independentWordMetricFlux (fun β => r • (H β - G β)) E α) +
        cellMetricFlux (r • (H [] - G [])) (E α)) +
          independentWordMetricFlux G (fun β => r • (E β - D β)) α)
      (r • (E α - D α)) := by
  have hd := cell_window_metric_quotient_solution J (G []) (H []) v hGsym hHsym
    (f α) (g α) (F α + independentWordMetricFlux G D α)
    (F' α + independentWordMetricFlux H E α) (D α) (E α) r hD hE
  have heq :
      r • ((F' α + independentWordMetricFlux H E α) -
        (F α + independentWordMetricFlux G D α)) + cellMetricFlux (r • (H [] - G [])) (E α) =
      (((r • (F' α - F α) + independentWordMetricFlux (fun β => r • (H β - G β)) E α) +
        cellMetricFlux (r • (H [] - G [])) (E α)) +
          independentWordMetricFlux G (fun β => r • (E β - D β)) α) := by
    rw [show (F' α + independentWordMetricFlux H E α) -
        (F α + independentWordMetricFlux G D α) =
      (F' α - F α) + (independentWordMetricFlux H E α - independentWordMetricFlux G D α)
      by abel]
    rw [smul_add, independentWordMetricFlux_quotient_split]
    abel
  rw [heq] at hd
  exact hd

end AVRegularity.WeakEntryProofs
end
end
end

section
section
/-! Genuine scalar drift and coefficient reserves give the actual weighted coefficient mean. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι]

def weightedCoefficientReserve (H m : ℕ) (c : LiftCoeff ι (fun _ => ℝ))
    (w : ℝ → Vec 2 → ℝ) (α : DerivativeWord2 m) (v u : ι)
    (Qw : JointSourceReserve H (fun t z _ => w t z))
    (Qc : JointSourceReserve H (fun t z Y => c m α t Y z v u 1)) :
    JointSourceReserve H
      (fun t z Y => weightedLiftCoefficientMean c w m α t Y z v u 1) := by
  let R := Qw.bilinear Qc (ContinuousLinearMap.lsmul ℝ ℝ)
  apply R.mean.congrSource
  funext t z Y
  have hc : Continuous (fun y => w t y • c m α t Y y v u) :=
    (Qw.fast_contDiff t Y).continuous.smul
      (realLinearMap_field_continuous_of_value_one _ (Qc.fast_contDiff t Y).continuous)
  have he := AVRegularity.fieldCellMean_clm (ContinuousLinearMap.apply ℝ ℝ 1) hc
  exact he

end AVRegularity.WeakEntryProofs
end
end

section
/-! The finite uncentered source depends only on earlier coefficient germs. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftALeftTerms_slow_local_primitive_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (Q Q' : LiftOperatorData ι h D)
    (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ) (hG : ∀ X ∈ Ω, Q.G t X = Q'.G t X) (v : ι)
    (hΓ : SlowOpenEdgeEq Ω t Q.edge Q'.edge)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q,
      ∀ α : DerivativeWord2 m, ∀ X ∈ Ω, ∀ z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u) :
    List.Forall₂ (LeftTermSlowEq Ω) (liftALeftTerms Q Cc hh n t v)
      (liftALeftTerms Q' Dc hh n t v) := by
  unfold liftALeftTerms
  rw [← hη, ← hv]
  apply List.rel_append
  · apply List.rel_append
    · apply cellB1LeftTerms_slow_local_metric_congr Ω hΩ Q.η (Q.G t) (Q'.G t) hG (Q.v t)
      exact liftComponentLeftTerms_slow_local_congr (n - 1) _ _ t v
        (fun m hm α X hX z u => he hh (n - 1)
          (Or.inr ⟨rfl, by omega⟩) m hm α X hX z v u)
    · by_cases hn2 : 2 ≤ n
      · simp only [ite_eq_left hn2]
        apply cellB2LeftTerms_slow_local_metric_congr Ω hΩ Q.η (Q.G t) (Q'.G t) hG
        exact liftComponentLeftTerms_slow_local_congr (n - 2) _ _ t v
          (fun m hm α X hX z u => he hh (n - 2)
            (Or.inr ⟨rfl, by omega⟩) m hm α X hX z v u)
      · simp only [ite_eq_right hn2]
        exact List.Forall₂.nil
  · by_cases hh0 : hh = 0
    · simp only [ite_eq_left hh0]
      exact List.Forall₂.nil
    · simp only [ite_eq_right hh0]
      apply List.rel_map (fun _ _ he => LeftTermSlowEq.smul he (-1))
      exact sourceConvolutionLeftTerms_slow_local_edge_congr Ω hΩ Q.edge Q'.edge Q.η t n _ _ v hΓ
        (fun q m hm α X hX z u u' => he (hh - 1) q (Or.inl (by omega))
          m hm α X hX z u u')

end AVRegularity.WeakEntryProofs
end
end

section
/-! The actual diagonal mean term list reproduces the full-cell mean. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] [DecidableEq ι] {D : ℕ}

theorem weakDiagonal_mean_left_terms_apply
    (Q : LiftOperatorData ι h D) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ 1 (fun X => Q.G t X i j))
    (hw : ∀ k, ContDiff ℝ 1 (fun z => Real.sqrt Q.η * Q.v t z k))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X z : Vec 2)
    (hc : ∀ k m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ v u,
      ContDiff ℝ 1 (fun Y => diagonalMeanFluxCoefficient Q Cc n k m α t Y 0 v u))
    (hfast : ∀ Y m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ v u,
      Continuous (fun y => Cc 0 (n - 1) m α t Y y v u))
    (hid : liftApply 0 (Cc 0 0) (fun _ => f) t = fun Y _ => f Y)
    (hΦ : GoodField 2 (liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t))
    (hΨ : 3 ≤ n → CoefField True 2 (liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => f) t)) :
    leftTermsApply (meanFluxLeftTerms n (diagonalMeanFluxCoefficient Q Cc n) t) f X z =
      liftMean Q Cc (fun _ => f) 0 n t X := by
  rw [meanFluxLeftTerms_apply n _ t hc f hf X z]
  have he (k : Fin 2) :
      (fun Y => liftApply (n - 1) (diagonalMeanFluxCoefficient Q Cc n k)
        (fun _ => f) t Y 0) = fun Y =>
      fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k) •
        liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t Y y) +
      if n = 2 then -Q.η • ∑ j : Fin 2, Q.G t Y k j • fderiv ℝ f Y (basisVec j) else 0 := by
    funext Y
    exact weakDiagonal_mean_flux_coefficient_vector_apply Q t (fun k => (hw k).continuous)
      Cc n hn f k Y 0 (hfast Y)
  simp_rw [he]
  by_cases hn2 : n = 2
  · subst n
    simp only [ite_true, neg_smul, ← sub_eq_add_neg]
    exact (weakLiftMean_diagonal_second Q t hG hw Cc f hf X hid hΦ).symm
  · simp only [ite_eq_right hn2, add_zero]
    exact (weakLiftMean_diagonal_ge_three Q t hG hw Cc f hf n (by omega) X hΦ (hΨ (by omega))).symm


end AVRegularity.WeakEntryProofs
end
end

section
/-! Finite genuine test reserves synthesize the exact scalar coefficient reserve. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def calibratedCoefficientReserve (H n m : ℕ) (hm : m ≤ n)
    (c : LiftCoeff ι (fun _ => ℝ))
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (v u : ι)
    (Q : ∀ p : Fin (m + 1) × Fin (n + 1), JointSourceReserve H
      (fun t z Y => normalizedLiftTestField c n
        ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) u v 1 t Y z)) :
    JointSourceReserve H (fun t z Y => c m α t Y z v u 1) := by
  exact (jointSourceReserve_scalar_coefficient_calibration H n m hm c hc α 1 one_ne_zero v u
    (fun p => by simpa only [one_smul] using Q p)).choose

end AVRegularity.WeakEntryProofs
end
end

section
/-! Finite calibration preserves genuine centering of every forcing test. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem calibratedCoefficient_mean_zero (H n m : ℕ) (hm : m ≤ n)
    (c : LiftCoeff ι (fun _ => ℝ))
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (v u : ι)
    (Q : ∀ p : Fin (m + 1) × Fin (n + 1), JointSourceReserve H
      (fun t z Y => normalizedLiftTestField c n
        ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) u v 1 t Y z))
    (hmean : ∀ p : Fin (m + 1) × Fin (n + 1), ∀ t Y,
      fieldCellMean (fun z => normalizedLiftTestField c n
        ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) u v 1 t Y z) = 0)
    (t : ℝ) (Y : Vec 2) : fieldCellMean (fun z => c m α t Y z v u 1) = 0 := by
  have he : (fun z => c m α t Y z v u 1) = fun z =>
      ∑ p : Fin (m + 1) × Fin (n + 1), liftCalibrationWeight n m α 1 p •
        normalizedLiftTestField c n ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) u v 1 t Y z := by
    funext z
    simpa only [one_smul] using (liftCalibration_synthesis n m hm c 1 one_ne_zero hc α t Y z v u 1).symm
  rw [he, fieldCellMean_sum Finset.univ
    (f := fun p z => liftCalibrationWeight n m α 1 p • normalizedLiftTestField c n
      ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) u v 1 t Y z)
    (fun p _ => by
      simpa only [Pi.smul_apply] using!
        ((Q p).fast_contDiff t Y).continuous.const_smul (liftCalibrationWeight n m α 1 p))]
  apply Finset.sum_eq_zero
  intro p _
  rw [fieldCellMean_smul, hmean p t Y, smul_zero]

end AVRegularity.WeakEntryProofs
end
end

section
/-! The actual Fourier construction for arbitrary scalar and flux Bochner L2 Hilbert data. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev

namespace AVRegularity.WeakEntryProofs
open AVRegularity.CycleEvolution AVRegularity.EntryWeakProofs

theorem molecular_exists_Hilbert_sources {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData) (S : ℝ → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b))) (F : ℝ → Fin 2 → ComplexCellL2)
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b))) (initial : ComplexCellL2) :
    ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice (fun t => dataDualDerivative P t
        (slice t) (S t) (F t)) ∧ u a = initial := by
  obtain ⟨src, hm, hs, he⟩ := cellBochner_exists_measurable_realization (Icc a b) S hS
  have hsrc := cellProduct_cellNormSq_finite (Icc a b) src hs
  have hex j := cellBochner_exists_measurable_realization (Icc a b) (fun t => F t j) (hF j)
  choose fj hjm hjs hje using hex
  let rawF := fun t x => WithLp.toLp 2 (fun j : Fin 2 => fj j t x)
  have hrawm : Measurable (Function.uncurry rawF) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℂ)).measurable.comp
      (Measurable.of_eval (fun j => hjm j))
  have hraw : MemLp (Function.uncurry rawF) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) :=
    cellFiniteArray_memLp (fun p : ℝ × Vec 2 => fun j => fj j p.1 p.2) hjs
  have henergy := cellProduct_cellNormSq_finite (Icc a b) rawF hraw
  obtain ⟨u, slice, h, hi⟩ := dataActual_exists_Hilbert hab P
    src rawF hm hrawm hsrc henergy initial
  refine ⟨u, slice, h.dual_congr ?_, hi⟩
  filter_upwards [he, ae_all_iff.mpr hje] with t ht htF
  have hc : (fun j => cellSourceSlice (fun τ x => rawF τ x j) t) = F t := by
    funext j
    exact htF j
  rw [ht, hc]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Full positive stored-weight sums bound all path products without a dimension-dependent norm. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Construction.Preservation.Ledger
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Stored size after conjugation by the square root of the prescribed weak masses. -/
def weakStoredEdgeWeight (G : GenStage D (fun _ => ℝ) Dm b j₀) (N J : ℕ) (η : ℝ)
    (e : LedgerEdge G) : ℝ :=
  Real.sqrt (weakMass D N J η e.2.1.1 / weakMass D N J η e.1.1) *
    (G.fam.identity e.1 e.2.1 e.2.2).record.size

def weakStoredTotal (G : GenStage D (fun _ => ℝ) Dm b j₀) (N J : ℕ) (η : ℝ) : ℝ :=
  ∑ e : LedgerEdge G, weakStoredEdgeWeight G N J η e

theorem weakStoredEdgeWeight_nonneg (G : GenStage D (fun _ => ℝ) Dm b j₀) (N J : ℕ) (η : ℝ)
    (e : LedgerEdge G) : 0 ≤ weakStoredEdgeWeight G N J η e :=
  mul_nonneg (Real.sqrt_nonneg _) (G.fam.identity e.1 e.2.1 e.2.2).record.size_nonneg

theorem weakStoredTotal_nonneg (G : GenStage D (fun _ => ℝ) Dm b j₀) (N J : ℕ) (η : ℝ) :
    0 ≤ weakStoredTotal G N J η :=
  Finset.sum_nonneg (fun e _ => weakStoredEdgeWeight_nonneg G N J η e)

/-- The square-root mass ratios cancel at every intermediate vertex. -/
theorem weakPath_stored_weight (G : GenStage D (fun _ => ℝ) Dm b j₀) (N J : ℕ) (η : ℝ)
    (hN : 1 ≤ N) (hJ : 1 ≤ J) (heps : ∀ i, 0 < D.eps i)
    (P : ProvParams) (ht : G.HasTags P) {n : ℕ} (π : StagePath G (n + 1)) :
    Real.sqrt (weakMass D N J η π.src / weakMass D N J η π.tgt) *
      (π.provList.map fun x => (x.2.2.tags P).witness).prod =
        pathWeight (weakStoredEdgeWeight G N J η) π := by
  let μ (v : CompIn G.comps) := weakMass D N J η v.1
  have hμ (v : CompIn G.comps) : 0 < μ v := weakMass_pos D N J η hN hJ heps v.1
  let a (v : CompIn G.comps) := (Real.sqrt (μ v))⁻¹
  have ha (v : CompIn G.comps) : 0 < a v := inv_pos.mpr (Real.sqrt_pos.mpr (hμ v))
  have hr (v u : CompIn G.comps) : a v / a u = Real.sqrt (μ u / μ v) := by
    rw [Real.sqrt_div (hμ u).le]
    change (Real.sqrt (μ v))⁻¹ / (Real.sqrt (μ u))⁻¹ = _
    rw [inv_div_inv]
  have hp := path_normalization_product a ha π
  simp only [pathWeight, hr] at hp
  have hsrc : π.src = (π.step 0).2.1.1 := by simp [StagePath.src]
  have htgt : π.tgt = (π.step (Fin.last n)).1.1 := by simp [StagePath.tgt, Fin.last]
  change (∏ i, Real.sqrt (μ (π.step i).2.1 / μ (π.step i).1)) =
    Real.sqrt (weakMass D N J η (π.step 0).2.1.1 /
      weakMass D N J η (π.step (Fin.last n)).1.1) at hp
  rw [← hsrc, ← htgt] at hp
  rw [EntryWeakProofs.stagePath_stored_witness_product G P ht π, ← hp,
    ← Finset.prod_mul_distrib]
  rfl

/-- Enlarging paths to arbitrary edge lists bounds the complete path sum by a power. -/
theorem weakStoredPath_sum_le (G : GenStage D (fun _ => ℝ) Dm b j₀) (N J : ℕ) (η : ℝ) (n : ℕ) :
    ∑ π : StagePath G n, pathWeight (weakStoredEdgeWeight G N J η) π ≤
      weakStoredTotal G N J η ^ n := by
  have hh := sum_comp_le (StagePath.step (G := G) (h := n))
    (stagePath_step_injective G n)
    (fun f : Fin n → LedgerEdge G => ∏ j, weakStoredEdgeWeight G N J η (f j))
    (fun f => Finset.prod_nonneg (fun j _ => weakStoredEdgeWeight_nonneg G N J η (f j)))
  have he : (∑ f : Fin n → LedgerEdge G, ∏ j, weakStoredEdgeWeight G N J η (f j)) =
      weakStoredTotal G N J η ^ n := by
    simpa only [weakStoredTotal, Fintype.piFinset_univ] using
      (Finset.sum_pow' (Finset.univ : Finset (LedgerEdge G))
        (weakStoredEdgeWeight G N J η) n).symm
  exact hh.trans_eq he

end AVRegularity.WeakEntryProofs
end
end

section
/-! The diagonal mean reserve includes the genuine molecular metric term at degree two. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def metricCoefficientReserve (H : ℕ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (QG : ∀ i j, JointSourceReserve H (fun t _ Y => G t Y i j))
    (k : Fin 2) (m : ℕ) (α : DerivativeWord2 m) (v u : ι) :
    JointSourceReserve H (fun t z Y =>
      metricFluxCoefficient (h := fun _ : ι => ℝ) η G k m α t Y z v u 1) := by
  cases m with
  | zero => exact JointSourceReserve.zero H
  | succ m =>
    cases m with
    | zero =>
      let c : ℝ := -η * blockIdentityEntry (fun _ : ι => ℝ) v u 1
      let R := (QG k (α 0)).map (c • ContinuousLinearMap.id ℝ ℝ)
      apply R.congrSource
      funext t z Y
      simp only [metricFluxCoefficient, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, c]
      ring
    | succ m => exact JointSourceReserve.zero H

def diagonalMeanCoefficientReserve (H : ℕ)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (n : ℕ)
    (k : Fin 2) (m : ℕ) (α : DerivativeWord2 m) (v u : ι)
    (QG : ∀ i j, JointSourceReserve H (fun t _ Y => Q.G t Y i j))
    (Qv : JointSourceReserve H (fun t z _ => Q.v t z k))
    (Qc : JointSourceReserve H (fun t z Y => Cc 0 (n - 1) m α t Y z v u 1)) :
    JointSourceReserve H (fun t z Y => diagonalMeanFluxCoefficient Q Cc n k m α t Y z v u 1) := by
  let Qw : JointSourceReserve H (fun t z (_ : Vec 2) => Real.sqrt Q.η * Q.v t z k) :=
    (Qv.map (Real.sqrt Q.η • ContinuousLinearMap.id ℝ ℝ)).congrSource (by
    funext t z Y
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul])
  let R := weightedCoefficientReserve H m (Cc 0 (n - 1))
    (fun t z => Real.sqrt Q.η * Q.v t z k) α v u Qw Qc
  by_cases hn : n = 2
  · apply (R.add (metricCoefficientReserve H Q.η Q.G QG k m α v u)).congrSource
    funext t z Y
    simp only [diagonalMeanFluxCoefficient, ite_eq_left hn, add_apply]
  · apply R.congrSource
    funext t z Y
    simp only [diagonalMeanFluxCoefficient, ite_eq_right hn, add_zero]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Exact mass-normalized weights of inherited weak means and fresh eddy means. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Construction.Preservation.Ledger
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The positive stored weight of a source, using its actual output endpoints. -/
def weakStoredSourceWeight (G : GenStage D (fun _ => ℝ) Dm b j₀) (N J : ℕ)
    (η : ℝ) (P : ProvParams) (rW : ℝ) (s : WeakSource G) : ℝ :=
  Real.sqrt (weakMass D N J η (s.srcComp G.level) / weakMass D N J η (s.tgtComp G.level)) *
    (s.weakTag P G.level rW η).size

/-- The same mass-normalized factor occurs on every fresh eddy edge of a passage. -/
def weakStoredEddyWeight (D : OCData) (N J : ℕ) (η : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt ((weakCw N J * D.eps (m - 1) ^ (η / 2))⁻¹) *
    (D.eps (m - 1) ^ (-η) * D.weakPe m ^ 2)

theorem weakStoredEddyWeight_nonneg (D : OCData) (N J : ℕ) (η : ℝ) (m : ℕ) :
    0 ≤ weakStoredEddyWeight D N J η m :=
by
  have heps : 0 ≤ D.eps (m - 1) := by
    unfold OCData.eps ocEpsilon
    split <;> positivity
  exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.rpow_nonneg heps _) (sq_nonneg _))

/-- Copying an inherited source into any word leaves its normalized path weight unchanged. -/
theorem weakStoredSourceWeight_inherited (G : GenStage D (fun _ => ℝ) Dm b j₀)
    (N J : ℕ) (η : ℝ) (hN : 1 ≤ N) (hJ : 1 ≤ J) (heps : ∀ i, 0 < D.eps i)
    (P : ProvParams) (ht : G.HasTags P) (rW : ℝ) (w : List WordLetter)
    (h : ℕ) (π : StagePath G (h + 1)) (n : ℕ) :
    weakStoredSourceWeight G N J η P rW (.inherited w (h + 1) π n) =
      pathWeight (weakStoredEdgeWeight G N J η) π := by
  have hb : 0 < weakCw N J * D.eps (G.level - 1) ^ (η / 2) :=
    mul_pos (weakCw_strict_pos N J hN hJ) (Real.rpow_pos_of_pos (heps _) _)
  have hratio : weakMass D N J η (succComp G.level π.src w) /
      weakMass D N J η (succComp G.level π.tgt w) =
        weakMass D N J η π.src / weakMass D N J η π.tgt := by
    rw [weakMass_succComp, weakMass_succComp]
    exact mul_div_mul_right _ _ (pow_ne_zero _ hb.ne')
  change Real.sqrt (weakMass D N J η (succComp G.level π.src w) /
    weakMass D N J η (succComp G.level π.tgt w)) * _ = _
  rw [hratio]
  exact weakPath_stored_weight G N J η hN hJ heps P ht π

/-- Appending one eddy letter contributes one mass factor and the stored eddy size. -/
theorem weakStoredSourceWeight_eddy (G : GenStage D (fun _ => ℝ) Dm b j₀)
    (N J : ℕ) (η : ℝ) (hN : 1 ≤ N) (hJ : 1 ≤ J) (heps : ∀ i, 0 < D.eps i)
    (P : ProvParams) (rW : ℝ) (v : CompIn G.comps) (w : List WordLetter) (n : ℕ) :
    weakStoredSourceWeight G N J η P rW (.eddy v w n) =
      weakStoredEddyWeight D N J η G.level := by
  have hb : 0 < weakCw N J * D.eps (G.level - 1) ^ (η / 2) :=
    mul_pos (weakCw_strict_pos N J hN hJ) (Real.rpow_pos_of_pos (heps _) _)
  have hμ := weakMass_pos D N J η hN hJ heps v.1
  have hratio : weakMass D N J η (succComp G.level v.1 w) /
      weakMass D N J η (succComp G.level v.1 (w ++ [.eddy n])) =
        (weakCw N J * D.eps (G.level - 1) ^ (η / 2))⁻¹ := by
    rw [weakMass_succComp, weakMass_succComp, List.length_append, List.length_singleton, pow_succ]
    field_simp [hμ.ne', hb.ne']
  exact congrArg (fun r => Real.sqrt r * (D.eps (G.level - 1) ^ (-η) * D.weakPe G.level ^ 2)) hratio

end AVRegularity.WeakEntryProofs
end
end

section
/-! Every actual raw ordered-word solution satisfies its literal Hilbert word equation. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {I : Type*}

theorem word_window_raw_to_Hilbert {a b : ℝ} (hab : a ≤ b) (N : ℕ) (P : MolecularData)
    (G : List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B : List I → ℝ)
    (src : List I → ℝ → Vec 2 → ℂ)
    (F : List I → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (c : List I → ℝ → RawJet2 1 ℂ)
    (hB : ∀ p, p.length ≤ N → 0 ≤ B p)
    (hm : ∀ p, p.length ≤ N → ∀ i j, Measurable (fun t => G p t i j))
    (hb : ∀ p, p.length ≤ N → ∀ t i j, |G p t i j| ≤ B p)
    (hsrc : ∀ p, p.length ≤ N → MemLp (Function.uncurry (src p)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : ∀ p, p.length ≤ N → MemLp (Function.uncurry (F p)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hsol : ∀ p, p.length ≤ N → IsCellSolution (Icc a b) (dataCoefficients P) (src p)
      (F p + independentWordMetricFlux (fun p t _ => G p t) c p) (c p))
    (w : List I) (hw : w.length ≤ N) :
    CellWeakHilbertCurve a b (cellRawTrace (c w)) (cellH1Slice (c w))
      (fun t => dataDualDerivative P t (cellH1Slice (c w) t) (cellSourceSlice (src w) t)
        (fun j => cellSourceSlice (fun s x => F w s x j) t +
          molecularWordHilbertFlux (fun p s => (G p s).transpose)
            (fun p => cellH1Slice (c p)) w t j)) := by
  have hl p (hp : p ∈ independentWordForcing w) := independentWordForcing_lengths w p hp
  have hg p (hp : p ∈ independentWordForcing w) : p.1.length ≤ N := by
    have hh := hl p hp
    omega
  have hc p (hp : p ∈ independentWordForcing w) : p.2.length ≤ N := by
    have hh := hl p hp
    omega
  have hword := word_metric_flux_window_memLp hab G c w B
    (fun p hp => hB p.1 (hg p hp)) (fun p hp => hm p.1 (hg p hp))
    (fun p hp => hb p.1 (hg p hp)) (dataCoefficients P) src
    (fun p => F p + independentWordMetricFlux (fun p t _ => G p t) c p)
    (fun p hp => hsol p.2 (hc p hp))
  have hcur := dataSolution_to_Hilbert hab P (src w)
    (F w + independentWordMetricFlux (fun p t _ => G p t) c w)
    (hsrc w hw) ((hF w hw).add hword) (c w) (hsol w hw)
  apply hcur.dual_congr
  have hgood : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ p ∈ independentWordForcing w, HasPeriodicOrderedWeakJet (c p.2 t) :=
    (Filter.eventually_all_finite (List.finite_toSet _)).mpr
      (fun p hp => (hsol p.2 (hc p hp)).2.1)
  have hFs (j : Fin 2) := cellSource_memLp_slices (Icc a b) (fun t x => F w t x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' (hF w hw))
  filter_upwards [hgood, (ae_all_iff.mpr hFs)] with t ht hFt
  apply congrArg (dataDualDerivative P t (cellH1Slice (c w) t) (cellSourceSlice (src w) t))
  funext j
  have he := wordMetricFlux_Hilbert_ae G c w t ht j
  have hmword : MemLp (fun x => independentWordMetricFlux (fun p s _ => G p s) c w t x j)
      2 (volume.restrict AVenhance.unitCube) := (memLp_congr_ae he).mp (Lp.memLp _)
  change cellSourceSlice (fun s x => F w s x j +
    independentWordMetricFlux (fun p r _ => G p r) c w s x j) t = _
  rw [cellSourceSlice_add_of_memLp _ _ t (hFt j) hmword,
    wordMetricFlux_sourceSlice_eq_Hilbert G c w t ht j]

end AVRegularity.WeakEntryProofs
end
end

section
/-! A bounded finite source code controls the complete positive weak-passage sum. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Construction.Preservation.Ledger
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

abbrev WeakStoredWords (N R : ℕ) :=
  {w : List WordLetter // w = [] ∨ w ∈ wordsUpTo (weakAlphabet N) R}

instance weakStoredWordsFintype (N R : ℕ) : Fintype (WeakStoredWords N R) := Fintype.ofFinite _

abbrev WeakStoredSourceCode (G : GenStage D (fun _ => ℝ) Dm b j₀) (N R Din H : ℕ) :=
  (WeakStoredWords N R × (Σ h : Fin H, StagePath G (h.1 + 1)) × Fin (N + Din + 1)) ⊕
    (CompIn G.comps × WeakStoredWords N R × Fin (N + 2))

def weakStoredCodeDecode (G : GenStage D (fun _ => ℝ) Dm b j₀) (N R Din H : ℕ) :
    WeakStoredSourceCode G N R Din H → WeakSource G
  | .inl (w, π, n) => .inherited w.1 (π.1.1 + 1) π.2 n.1
  | .inr (v, w, n) => .eddy v w.1 n.1

theorem weakStoredCode_covers (G : GenStage D (fun _ => ℝ) Dm b j₀) (N R Din H : ℕ)
    (hpath : ∀ h, StagePath G h → h ≤ H) (s : WeakSource G) (hs : s.Valid N R Din) :
    ∃ c : WeakStoredSourceCode G N R Din H, weakStoredCodeDecode G N R Din H c = s := by
  cases s with
  | inherited w h π n =>
    obtain ⟨hw, hh, hn, hn'⟩ := hs
    cases h with
    | zero => omega
    | succ h =>
      exact ⟨.inl (⟨w, hw⟩, ⟨⟨h, by have := hpath (h + 1) π; omega⟩, π⟩,
        ⟨n, by omega⟩), rfl⟩
  | eddy v w n =>
    obtain ⟨hw, _, _, hn⟩ := hs
    exact ⟨.inr (v, ⟨w, hw⟩, ⟨n, by omega⟩), rfl⟩

/-- The output edge-to-source bijections are globally injective because a source fixes both
endpoints. No component-count loss occurs when enlarging to the finite source code. -/
theorem weakStoredTotal_le_code (P : ProvParams) (Mn : WeakMenu) (J Din H : ℕ)
    (rW : ℝ) (G G' : GenStage D (fun _ => ℝ) Dm b j₀)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G.HasTags P) (ht' : G'.HasTags P)
    (hN : 1 ≤ Mn.N) (hJ : 1 ≤ J) (heps : ∀ i, 0 < D.eps i)
    (hpath : ∀ h, StagePath G h → h ≤ H) :
    weakStoredTotal G' Mn.N J Mn.η0 ≤
      ∑ c : WeakStoredSourceCode G Mn.N Mn.R Din H,
        weakStoredSourceWeight G Mn.N J Mn.η0 P rW (weakStoredCodeDecode G Mn.N Mn.R Din H c) := by
  obtain ⟨_, _, _, _, _, e, idx, Cc, Cc0, _, _, _, hd⟩ := hp
  let src (a : LedgerEdge G') : WeakSource G := (e a.1 a.2.1 a.2.2).1
  have hv (a : LedgerEdge G') : (src a).Valid Mn.N Mn.R Din := (e a.1 a.2.1 a.2.2).2.1
  have hinj : Function.Injective src := by
    rintro ⟨v, u, γ⟩ ⟨v', u', γ'⟩ hh
    have htarget : v = v' := Subtype.ext ((e v u γ).2.2.2.symm.trans
      ((congrArg (WeakSource.tgtComp G.level) hh).trans (e v' u' γ').2.2.2))
    have hsource : u = u' := Subtype.ext ((e v u γ).2.2.1.symm.trans
      ((congrArg (WeakSource.srcComp G.level) hh).trans (e v' u' γ').2.2.1))
    subst v'
    subst u'
    have hγ : γ = γ' := (e v u).injective (Subtype.ext hh)
    subst γ'
    rfl
  let code (a : LedgerEdge G') := (weakStoredCode_covers G Mn.N Mn.R Din H hpath (src a) (hv a)).choose
  have hc (a : LedgerEdge G') : weakStoredCodeDecode G Mn.N Mn.R Din H (code a) = src a :=
    (weakStoredCode_covers G Mn.N Mn.R Din H hpath (src a) (hv a)).choose_spec
  have hcode : Function.Injective code := by
    intro a b hab
    exact hinj ((hc a).symm.trans ((congrArg (weakStoredCodeDecode G Mn.N Mn.R Din H) hab).trans (hc b)))
  have hw (a : LedgerEdge G') : weakStoredEdgeWeight G' Mn.N J Mn.η0 a =
      weakStoredSourceWeight G Mn.N J Mn.η0 P rW (src a) := by
    have hh := ht' a.1 a.2.1 a.2.2
    rw [(hd a.1 a.2.1 a.2.2).1] at hh
    change Real.sqrt (_ / _) * _ = Real.sqrt (_ / _) * _
    rw [hh.1.1, (e a.1 a.2.1 a.2.2).2.2.1, (e a.1 a.2.1 a.2.2).2.2.2]
    rfl
  have hn (c : WeakStoredSourceCode G Mn.N Mn.R Din H) :
      0 ≤ weakStoredSourceWeight G Mn.N J Mn.η0 P rW (weakStoredCodeDecode G Mn.N Mn.R Din H c) := by
    rcases c with ⟨w, π, n⟩ | ⟨v, w, n⟩
    · rw [weakStoredCodeDecode, weakStoredSourceWeight_inherited G Mn.N J Mn.η0 hN hJ heps P ht]
      exact pathWeight_nonneg _ (weakStoredEdgeWeight_nonneg G Mn.N J Mn.η0) _
    · rw [weakStoredCodeDecode, weakStoredSourceWeight_eddy G Mn.N J Mn.η0 hN hJ heps]
      exact weakStoredEddyWeight_nonneg D Mn.N J Mn.η0 G.level
  have hh := sum_comp_le code hcode
    (fun c => weakStoredSourceWeight G Mn.N J Mn.η0 P rW (weakStoredCodeDecode G Mn.N Mn.R Din H c)) hn
  simpa only [weakStoredTotal, hc, ← hw] using hh

/-- The inherited part costs a fixed word/degree count and powers of the incoming total;
the eddy part costs a fixed word/degree count times the incoming component count. -/
theorem weakStoredTotal_passage_le (P : ProvParams) (Mn : WeakMenu) (J Din H : ℕ)
    (rW : ℝ) (G G' : GenStage D (fun _ => ℝ) Dm b j₀)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G.HasTags P) (ht' : G'.HasTags P)
    (hN : 1 ≤ Mn.N) (hJ : 1 ≤ J) (heps : ∀ i, 0 < D.eps i)
    (hpath : ∀ h, StagePath G h → h ≤ H) :
    weakStoredTotal G' Mn.N J Mn.η0 ≤
      (Fintype.card (WeakStoredWords Mn.N Mn.R) : ℝ) * (Mn.N + Din + 1) *
        ∑ h : Fin H, weakStoredTotal G Mn.N J Mn.η0 ^ (h.1 + 1) +
      (Fintype.card (CompIn G.comps) : ℝ) * Fintype.card (WeakStoredWords Mn.N Mn.R) *
        (Mn.N + 2) * weakStoredEddyWeight D Mn.N J Mn.η0 G.level := by
  refine (weakStoredTotal_le_code P Mn J Din H rW G G' hp ht ht' hN hJ heps hpath).trans ?_
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma, weakStoredCodeDecode,
    weakStoredSourceWeight_inherited G Mn.N J Mn.η0 hN hJ heps P ht,
    weakStoredSourceWeight_eddy G Mn.N J Mn.η0 hN hJ heps P rW,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, ← Finset.mul_sum]
  have hpows : (∑ h : Fin H, ∑ π : StagePath G (h.1 + 1),
      pathWeight (weakStoredEdgeWeight G Mn.N J Mn.η0) π) ≤
      ∑ h : Fin H, weakStoredTotal G Mn.N J Mn.η0 ^ (h.1 + 1) :=
    Finset.sum_le_sum (fun h _ => weakStoredPath_sum_le G Mn.N J Mn.η0 (h.1 + 1))
  have hh := mul_le_mul_of_nonneg_left hpows
    (by positivity : 0 ≤ (Fintype.card (WeakStoredWords Mn.N Mn.R) : ℝ) * (Mn.N + Din + 1))
  nlinarith only [hh]

end AVRegularity.WeakEntryProofs
end
end
end
