-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.MolecularRawSpatialEquation
public import AVRegularity.Definitions.EntryWeak.WeakReduction
public import AVRegularity.CycleEvolution.CellTimeMetricDriftCLM
import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePrimitiveContinuity
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
public import AVRegularity.CoupledEnergy.Galerkin.TorusBandSourceIntegrand
import AVRegularity.Construction.EntryScales.TerminalCore

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Each literal inherited flux factor preserves the edge and input amplitudes separately. -/

variable {ι : Type*}

def sourceCovariantWordConstant (A : Vec 2 →L[ℝ] ℝ) (η : ℝ) : ℝ :=
  1 + ‖Real.sqrt η • ContinuousLinearMap.id ℝ ℝ‖ * (1 + ‖A‖)

def normalizedSourceFluxTermBudget (H D : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η BE BF : ℝ) : ℝ :=
  ‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ H * BE *
    (sourceCovariantWordConstant A η ^ D * BF)

theorem sourceCovariantWordConstant_one_le (A : Vec 2 →L[ℝ] ℝ) (η : ℝ) :
    1 ≤ sourceCovariantWordConstant A η :=
  le_add_of_nonneg_right
    (mul_nonneg (norm_nonneg _) (add_nonneg zero_le_one (norm_nonneg A)))

theorem normalizedSourceFluxTermBudget_nonneg (H D : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BE BF : ℝ) (hBE : 0 ≤ BE) (hBF : 0 ≤ BF) :
    0 ≤ normalizedSourceFluxTermBudget H D A η BE BF := by
  unfold normalizedSourceFluxTermBudget sourceCovariantWordConstant
  positivity

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Generator convergence for the actual raw Galerkin state curves. -/

variable {a b : ℝ} {hab : a ≤ b} {P : MolecularData}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {initial : ComplexCellL2}

/-- The raw periodic H¹ state of one actual finite path. -/
def MolecularGalerkinLimitData.state
    (D : MolecularGalerkinLimitData a b hab P src F initial) (N : ℕ) (t : ℝ) :
    TorusHk 1 ℂ := (extendCurve hab (D.curve N) t).val

/-- The temporal H¹ class of one actual finite state. -/
def MolecularGalerkinLimitData.stateClass
    (D : MolecularGalerkinLimitData a b hab P src F initial) (N : ℕ) : CellBochnerH1 a b :=
  (D.stateLp N).toLp (D.state N)

/-- Generator integrals of actual raw finite states converge with the projected test. -/
theorem MolecularGalerkinLimitData.generator_integral_tendsto
    (D : MolecularGalerkinLimitData a b hab P src F initial)
    (z : TorusHk 1 ℂ) (t : ℝ) (ht : t ∈ Icc a b) :
    Tendsto (fun n => ∫ r in a..t, dataGeneratorForm P r
      (D.state (D.subsequence n) r) (galerkinProj (D.subsequence n) z)) atTop
      (𝓝 (∫ r in a..t, dataGeneratorForm P r (D.limit r) z)) := by
  let L := dataGeneratorIntegralTestCLM hab ⟨le_rfl, hab⟩ ht ht.1 P
  have htest := (L.continuous.tendsto z).comp
    ((galerkinProj_tendsto z).comp D.monotone.tendsto_atTop)
  have he := cellWeak_eval_perturbed_test (fun n => D.stateClass (D.subsequence n)) D.limit
    D.budget (fun n => D.norm_bound (D.subsequence n)) D.weak
    (fun n => L (galerkinProj (D.subsequence n) z)) (L z) htest
  have hr : L z D.limit = ∫ r in a..t, dataGeneratorForm P r (D.limit r) z :=
    dataGeneratorIntegralCLM_apply_class ⟨le_rfl, hab⟩ ht ht.1 P z D.limit
  rw [hr] at he
  apply he.congr'
  filter_upwards with n
  exact (dataGeneratorIntegralCLM_apply ⟨le_rfl, hab⟩ ht ht.1 P
    (galerkinProj (D.subsequence n) z) (D.state (D.subsequence n)) (D.stateLp (D.subsequence n)))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Actual physical fluxes are unchanged by genuine local primitive extensions. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftFluxX_edge_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U)
    (Q : LiftOperatorData ι h D) (edge : ConstituentEdges D h)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) (hΓ : SlowOpenEdgeEq U t Q.edge edge) (k : Fin 2) :
    SlowOpenFieldEq U (fun X z => liftFluxX Q Cc f hh n t X z k)
      (fun X z => liftFluxX {Q with edge := edge} Cc f hh n t X z k) := by
  intro X hX z
  have htail : (if hh = 0 then 0 else ∑ j ∈ Finset.Icc 1 (min D n),
      (Real.sqrt Q.η * ((j - 1).factorial : ℝ)⁻¹) • iteratedDeriv (j - 1)
        (fun ε => sourceFlux Q.edge Q.η ε t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) k X z) 0) =
      (if hh = 0 then 0 else ∑ j ∈ Finset.Icc 1 (min D n),
      (Real.sqrt Q.η * ((j - 1).factorial : ℝ)⁻¹) • iteratedDeriv (j - 1)
        (fun ε => sourceFlux edge Q.η ε t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) k X z) 0) := by
    by_cases hhh : hh = 0
    · rw [ite_eq_left hhh, ite_eq_left hhh]
    · rw [ite_eq_right hhh, ite_eq_right hhh]
      apply Finset.sum_congr rfl
      intro j _
      have he : (fun ε => sourceFlux Q.edge Q.η ε t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) k X z) =
          fun ε => sourceFlux edge Q.η ε t
            (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) k X z := by
        funext ε
        exact sourceFlux_slow_open_congr hU (fun _ _ _ => rfl) Q.η ε t hΓ k X hX z
      rw [he]
  unfold liftFluxX
  dsimp only
  rw [htail]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! Word length supplies an explicit rank for the weak component graph. -/

def weakComponentRank (c : Comp) : ℕ := (c.births.map fun e => e.word.length).sum

theorem weakComponentRank_succComp (m : ℕ) (c : Comp) (w : List WordLetter) :
    weakComponentRank (succComp m c w) = weakComponentRank c + w.length := by
  by_cases hw : w = []
  · subst w
    simp [succComp]
  · simp [succComp, hw, weakComponentRank, Nat.add_comm]

theorem wordsOfLength_length (A : Finset WordLetter) (n : ℕ)
    (w : List WordLetter) (hw : w ∈ wordsOfLength A n) : w.length = n := by
  induction n generalizing w with
  | zero =>
      have he : w = [] := by simpa only [wordsOfLength, Finset.mem_singleton] using hw
      subst w
      rfl
  | succ n ih =>
      obtain ⟨⟨a, v⟩, hv, rfl⟩ := Finset.mem_image.mp hw
      have hl := ih v (Finset.mem_product.mp hv).2
      simp only [List.length_append, List.length_singleton, hl]

theorem wordsUpTo_length_le (A : Finset WordLetter) (R : ℕ)
    (w : List WordLetter) (hw : w ∈ wordsUpTo A R) : w.length ≤ R := by
  obtain ⟨n, hn, hw⟩ := Finset.mem_biUnion.mp hw
  rw [wordsOfLength_length A n w hw]
  exact (Finset.mem_Icc.mp hn).2

theorem weakExtComps_rank_bound (m N R B : ℕ) (S : Finset Comp)
    (hS : ∀ c ∈ S, weakComponentRank c ≤ B) :
    ∀ c ∈ weakExtComps m N R S, weakComponentRank c ≤ B + R := by
  intro c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · exact (hS c hc).trans (Nat.le_add_right B R)
  · obtain ⟨⟨v, w⟩, hvw, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hv, hw⟩ := Finset.mem_product.mp hvw
    rw [weakComponentRank_succComp]
    exact Nat.add_le_add (hS v hv) (wordsUpTo_length_le _ _ _ hw)

/-! The actual weak recursion has its stated levels and native output charts. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakConstruction_level (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (stage : ℕ → GenStage D hr Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage)
    (i : ℕ) (hi : M ≤ i) (hit : i ≤ M + J) : (stage i).level = i := by
  have main : ∀ n, n ≤ J → (stage (M + J - n)).level = M + J - n := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa only [Nat.sub_zero] using hc.2.1.1
    | succ n ih =>
        intro hn
        have hp := (hc.2.2 (M + J - n) (by omega) (by omega)).1.2.1
        have heq : M + J - n - 1 = M + J - (n + 1) := by omega
        rw [ih (by omega), heq] at hp
        exact hp
  have heq : M + J - (M + J - i) = i := by omega
  simpa only [heq] using main (M + J - i) (by omega)

theorem weakConstruction_output_natural (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (stage : ℕ → GenStage D hr Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage)
    (i : ℕ) (hi : M ≤ i) (hit : i < M + J) : (stage i).IsNatural (M + J) := by
  have hp := (hc.2.2 (i + 1) (by omega) (by omega)).1.2.2.2.2.1
  simpa only [Nat.add_sub_cancel, hc.1] using hp
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! Actual weak outgoing maps retain the scalar identity-map norm, independently of record sizes. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem rootPathMap_empty_norm_le_one (a c : ℕ) : ‖rootPathMap hr a [] c‖ ≤ 1 := by
  by_cases h : a = c
  · subst c
    simp only [rootPathMap]
    exact ContinuousLinearMap.norm_id_le
  · simp only [rootPathMap, dite_eq_right h, norm_zero]
    exact zero_le_one

theorem weakPassage_identity_map_norm_le_one (P : ProvParams) (Mn : WeakMenu)
    (rW : ℝ) (Din : ℕ) (G G' : GenStage D hr Dm b j₀)
    (hp : IsWeakPassage D P Mn rW Din G G')
    (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) :
    ‖(G'.fam.identity v u γ).map‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, e, idx, Cc, Cc0, _, _, _, he⟩ := hp
  rw [(he v u γ).2.1]
  exact rootPathMap_empty_norm_le_one _ _

theorem weakConstruction_identity_map_norm_le_one (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (stage : ℕ → GenStage D hr Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage)
    (i : ℕ) (hi : M ≤ i) (hit : i < M + J)
    (v u : CompIn (stage i).comps) (γ : (stage i).fam.Γ v u) :
    ‖((stage i).fam.identity v u γ).map‖ ≤ 1 := by
  have hp := (hc.2.2 (i + 1) (by omega) (by omega)).1
  have he : i + 1 - 1 = i := by omega
  rw [he] at hp
  exact weakPassage_identity_map_norm_le_one P Mn rW _ _ _ hp v u γ

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! The actual weak seed tags impose the prescribed finite outgoing degree bound. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakSource_degree_le {G : GenStage D hr Dm b j₀}
    (s : WeakSource G) (N R Din : ℕ) (hDin : 1 ≤ Din) (hs : s.Valid N R Din) :
    s.degree ≤ N + Din := by
  cases s with
  | inherited w h π n => exact hs.2.2.2
  | eddy v w n =>
    have hn : n ≤ N + 1 := hs.2.2.2
    exact hn.trans (Nat.add_le_add_left hDin N)

theorem weakSource_tag_order {G : GenStage D hr Dm b j₀}
    (s : WeakSource G) (P : ProvParams) (m : ℕ) (rW η : ℝ) :
    (s.weakTag P m rW η).maxOrder = s.degree := by
  cases s <;> rfl

theorem weakPassage_output_order_bound (P : ProvParams) (Mn : WeakMenu)
    (rW : ℝ) (Din : ℕ) (hDin : 1 ≤ Din) (G G' : GenStage D hr Dm b j₀)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P) :
    G'.maxOrderBound (Mn.N + Din) := by
  obtain ⟨_, _, _, _, _, e, idx, Cc, Cc0, _, _, _, he⟩ := hp
  intro v u γ
  have ho := (ht v u γ).2
  rw [(he v u γ).1] at ho
  change (G'.fam.identity v u γ).maxOrder =
    ((e v u γ).1.weakTag P G.level rW Mn.η0).maxOrder at ho
  rw [weakSource_tag_order] at ho
  rw [ho]
  exact weakSource_degree_le (e v u γ).1 Mn.N Mn.R Din hDin (e v u γ).2.1

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Centered real data give a centered classical representative of the molecular trace. -/

theorem realCellMean_zero (q : Vec 2 → ℝ) (hq : ∫ x in AVenhance.unitCube, q x = 0) :
    cellMean (fun x => (q x : ℂ)) = 0 := by
  change (∫ x in AVenhance.unitCube, (q x : ℂ)) = 0
  rw [integral_complex_ofReal, hq, Complex.ofReal_zero]

theorem dataWeak_classical_mean_zero {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData) (hv : IsCellDrift P.v)
    (g : ℝ → Vec 2 → ℝ)
    (hg : MemLp (fun p : ℝ × Vec 2 => (g p.1 p.2 : ℂ)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hgm : ∀ t, ∫ x in AVenhance.unitCube, g t x = 0)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => dataDualDerivative P t
      (slice t) (cellSourceSlice (fun r x => (g r x : ℂ)) t)
      (fun j => cellSourceSlice (fun _ _ => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)) j) t)))
    (hi : cellMean (u a) = 0) (c : ℝ → Vec 2 → ℝ)
    (he : ∀ t ∈ Icc a b, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (c t x : ℂ)) :
    ∀ t ∈ Icc a b, cellMean (fun x => (c t x : ℂ)) = 0 := by
  have hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      cellMean (cellSourceSlice (fun r x => (g r x : ℂ)) t) = 0 := by
    filter_upwards [cellSource_memLp_slices (Icc a b) (fun r x => (g r x : ℂ)) hg] with t ht
    exact (integral_congr_ae (cellSourceSlice_ae _ t ht)).trans (realCellMean_zero _ (hgm t))
  have hm := dataWeak_mean_conserved hab P hv u slice _ _ h hs
  intro t ht
  exact (integral_congr_ae (he t ht).symm).trans ((hm t ht).trans hi)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Higher traces of actual raw solutions supply measurable bounded carriers on their window. -/

theorem rawHigherWindowCarrier_exists {a b : ℝ} (hab : a ≤ b)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ} {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellSolution (Icc a b) C src flux D)
    (K : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hb : ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ,
      torusHkValueCLM w = cellRawTrace D t ∧ ‖w‖ ≤ R) :
    ∃ w : ℝ → TorusHk K ℂ, StronglyMeasurable w ∧ (∀ t, ‖w t‖ ≤ R) ∧
      ∀ t ∈ Icc a b, torusHkValueCLM (w t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t := by
  let clamp := fun t : ℝ => max a (min b t)
  have hc : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have hi (t : ℝ) : clamp t ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have he (t : ℝ) (ht : t ∈ Icc a b) : clamp t = t := by
    dsimp only [clamp]
    rw [min_eq_right ht.2, max_eq_right ht.1]
  have hu : Continuous (fun t => cellRawTrace D (clamp t)) :=
    (cellRawTrace_continuous (Icc a b) D (fun t ht => (hD.2.2.1 t ht).1)
      hD.2.2.2.2.1).comp_continuous hc hi
  obtain ⟨w, hm, hw, hn⟩ := higherWindowCarrier_exists K (Icc a b) measurableSet_Icc
    (fun t => cellRawTrace D (clamp t)) hu.stronglyMeasurable R hR (fun t ht => by
      rw [he t ht]
      exact hb t ht)
  refine ⟨w, hm, hn, ?_⟩
  intro t ht
  rw [hw t, indicator_of_mem ht, he t ht]
  exact cellRawTrace_ae D t (hD.2.2.1 t ht).1

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Every actual weak output has degree bounded by the fixed menu, independently of the ambient cap. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakConstruction_output_maxOrder_bound (P : ProvParams) (Mn : WeakMenu)
    (M J : ℕ) (rW : ℝ) (r : ℕ) (stage : ℕ → GenStage D hr Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage)
    (i : ℕ) (hi : M ≤ i) (hit : i < M + J) :
    (stage i).maxOrderBound (1 + J * Mn.N) := by
  have hp := hc.2.2 (i + 1) (by omega) (by omega)
  have ho := weakPassage_output_order_bound P Mn rW (1 + (M + J - (i + 1)) * Mn.N)
    (by omega) (stage (i + 1)) (stage ((i + 1) - 1)) hp.1 hp.2
  simp only [Nat.add_sub_cancel] at ho
  have hm : (M + J - (i + 1) + 1) * Mn.N ≤ J * Mn.N :=
    Nat.mul_le_mul_right Mn.N (by omega)
  rw [Nat.add_mul, one_mul] at hm
  intro v u γ
  exact (ho v u γ).trans (by omega)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! Every inherited weak path increases word rank, giving a finite grade bound. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem stagePath_rank_span (G : GenStage D hr Dm b j₀)
    (he : ∀ (v u : CompIn G.comps), G.fam.Γ v u → weakComponentRank u.1 < weakComponentRank v.1)
    (h : ℕ) (hh : 1 ≤ h) (π : StagePath G h) :
    weakComponentRank π.src + h ≤ weakComponentRank π.tgt := by
  have hp : 0 < h := by omega
  have main : ∀ j (hj : j < h),
      weakComponentRank (π.step ⟨0, hp⟩).2.1.1 + j + 1 ≤
        weakComponentRank (π.step ⟨j, hj⟩).1.1 := by
    intro j
    induction j with
    | zero =>
        intro hj
        exact he _ _ (π.step ⟨0, hj⟩).2.2
    | succ j ih =>
        intro hj
        have hj' : j < h := by omega
        have hi := ih hj'
        have hb := he _ _ (π.step ⟨j + 1, hj⟩).2.2
        have hjn := congrArg (fun c : CompIn G.comps => weakComponentRank c.1) (π.joined j hj)
        omega
  have hx := main (h - 1) (by omega)
  simpa only [StagePath.src, StagePath.tgt, dite_eq_left hp,
    Nat.add_assoc, Nat.sub_add_cancel hh] using hx

theorem stagePath_length_le_rank_bound (G : GenStage D hr Dm b j₀)
    (he : ∀ (v u : CompIn G.comps), G.fam.Γ v u → weakComponentRank u.1 < weakComponentRank v.1)
    (B : ℕ) (hB : ∀ c ∈ G.comps, weakComponentRank c ≤ B)
    (h : ℕ) (π : StagePath G h) : h ≤ B := by
  by_cases hh : h = 0
  · subst h
    exact Nat.zero_le _
  · have hp : 0 < h := Nat.pos_of_ne_zero hh
    have ht : π.tgt ∈ G.comps := by
      simpa only [StagePath.tgt, dite_eq_left hp] using (π.step ⟨h - 1, by omega⟩).1.2
    have hs := stagePath_rank_span G he h (by omega) π
    have hb := hB π.tgt ht
    omega

theorem weakSource_strict_rank (G : GenStage D hr Dm b j₀)
    (he : ∀ (v u : CompIn G.comps), G.fam.Γ v u → weakComponentRank u.1 < weakComponentRank v.1)
    (N R Din : ℕ) (s : WeakSource G) (hs : s.Valid N R Din) :
    weakComponentRank (s.srcComp G.level) < weakComponentRank (s.tgtComp G.level) := by
  cases s with
  | inherited w h π n =>
      have hp := stagePath_rank_span G he h hs.2.1 π
      simp only [WeakSource.srcComp, WeakSource.tgtComp, weakComponentRank_succComp]
      have hh : 1 ≤ h := hs.2.1
      omega
  | eddy v w n =>
      simp only [WeakSource.srcComp, WeakSource.tgtComp, weakComponentRank_succComp,
        List.length_append, List.length_singleton]
      omega

theorem weakPassage_strict_rank (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (G G' : GenStage D hr Dm b j₀) (hp : IsWeakPassage D P Mn rW Din G G')
    (he : ∀ (v u : CompIn G.comps), G.fam.Γ v u → weakComponentRank u.1 < weakComponentRank v.1) :
    ∀ (v u : CompIn G'.comps), G'.fam.Γ v u → weakComponentRank u.1 < weakComponentRank v.1 := by
  obtain ⟨_, _, _, _, _, e, _, _, _, _, _, _, _⟩ := hp
  intro v u γ
  have hs := (e v u γ).2
  have hh := weakSource_strict_rank G he Mn.N Mn.R Din (e v u γ).1 hs.1
  rw [hs.2.1, hs.2.2] at hh
  exact hh

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Weak inherited amplitudes are exactly the product of the incoming stored record sizes. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem stagePath_stored_witness_product (G : GenStage D hr Dm b j₀)
    (P : ProvParams) (ht : G.HasTags P) {h : ℕ} (π : StagePath G h) :
    (π.provList.map (fun x => (x.2.2.tags P).witness)).prod =
      ∏ j : Fin h, (G.fam.identity _ _ (π.step j).2.2).record.size := by
  rw [StagePath.provList, List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro j _
  exact (ht _ _ (π.step j).2.2).1.1.symm

theorem stagePath_stored_witness_nonneg (G : GenStage D hr Dm b j₀)
    (P : ProvParams) (ht : G.HasTags P) {h : ℕ} (π : StagePath G h) :
    0 ≤ (π.provList.map (fun x => (x.2.2.tags P).witness)).prod := by
  rw [stagePath_stored_witness_product G P ht π]
  exact Finset.prod_nonneg (fun j _ => (G.fam.identity _ _ (π.step j).2.2).record.size_nonneg)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Literal cell means retain a genuine finite slow source reserve and its uniform bound. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def JointSourceReserve.mean {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) :
    JointSourceReserve H (fun t _ Y => fieldCellMean (fun z => f t z Y)) := by
  have hbox (t : ℝ) : IsBoxSmooth H 0 (fun Y z => f t z Y) := by
    have hswap : ContDiff ℝ (H : ℕ∞) (Prod.swap : Vec 2 × Vec 2 → Vec 2 × Vec 2) :=
      contDiff_snd.prodMk contDiff_fst
    apply Weighted.isBoxSmooth_of_joint_contDiff
    convert (Q.regular t).comp hswap using 1
    · norm_cast
  have hmean (n : ℕ) (hn : n ≤ H) (t : ℝ) :
      ContDiff ℝ (H : ℕ∞) (fun Y => fieldCellMean (fun z => f t z Y)) ∧
      ∀ Y, ‖iteratedFDeriv ℝ n (fun Y => fieldCellMean (fun z => f t z Y)) Y‖ ≤
        2 ^ n * Q.budget n := by
    have hb := CycleComparison.Lift.fieldCellMean_graded_jet_bound H n 0 0 hn
      (fun Y z => f t z Y) (hbox t) Q.budget 1
      (fun j hj Y z => by simpa only [one_pow, mul_one] using Q.slow_derivative_bound j hj t z Y)
    simpa only [one_pow, mul_one] using hb
  refine ⟨?_, (fun _ _ _ _ => rfl), ?_, (fun n => 2 ^ n * Q.budget n),
    (fun n => mul_nonneg (by positivity) (Q.budget_nonneg n)), ?_⟩
  · intro t
    exact (hmean 0 (Nat.zero_le _) t).1.comp contDiff_snd
  · intro Y
    have hm : Measurable (fun t => fieldCellMean (fun z => f t z Y)) :=
      CycleComparison.Lift.fieldCellMean_parameter_measurable (fun t z => f t z Y)
        (fun z => (Q.measurable Y).comp (measurable_id.prodMk measurable_const))
        (fun t => (Q.fast_contDiff t Y).continuous)
    exact hm.comp measurable_fst
  · intro n hn t X
    let L := ContinuousLinearMap.snd ℝ (Vec 2) (Vec 2)
    have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun U => by
        change ‖U.2‖ ≤ 1 * ‖U‖
        simpa only [one_mul] using norm_snd_le U)
    have hb := finite_realWordJet_affine_derivative_bound
      (fun Y => fieldCellMean (fun z => f t z Y)) 0 n
      ((hmean n hn t).1.of_le (by exact_mod_cast (show 0 + n ≤ H by omega)))
      Fin.elim0 (fun i => Fin.elim0 i) L hL 0 X
    have he : (fun U => realWordJet (fun Y => fieldCellMean (fun z => f t z Y))
        0 Fin.elim0 (L U + 0)) = fun U : Vec 2 × Vec 2 => fieldCellMean (fun z => f t z U.2) := by
      funext U
      rw [realWordJet, iteratedFDeriv_zero_apply]
      rw [add_zero]
      rfl
    rw [he, zero_add, add_zero] at hb
    exact hb.trans ((hmean n hn t).2 X.2)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! The physical path flux depends only on genuine earlier coefficient germs on the open carrier. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftFluxX_slow_open_congr_predecessors {U : Set (Vec 2)} (hU : IsOpen U)
    (Q : LiftOperatorData ι h D) (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (hn : 2 ≤ n) (t : ℝ)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m ≤ q, ∀ α X, X ∈ U → ∀ z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u)
    (X : Vec 2) (hX : X ∈ U) (z : Vec 2) (k : Fin 2) :
    liftFluxX Q Cc f hh n t X z k = liftFluxX Q Dc f hh n t X z k := by
  have hop (p q : ℕ) (hpq : p < hh ∨ (p = hh ∧ q < n)) :
      SlowOpenFieldEq U (liftApply q (Cc p q) f t) (liftApply q (Dc p q) f t) :=
    liftApply_slow_open_congr hU q t _ _ f f (he p q hpq) (fun _ _ => rfl)
  have h₁ := hop hh (n - 1) (Or.inr ⟨rfl, by omega⟩)
  have h₂ := hop hh (n - 2) (Or.inr ⟨rfl, by omega⟩)
  have hf j := h₁.fastPartial j X hX z
  have hs j := h₂.slowPartial hU j X hX z
  have hS : (if hh = 0 then 0 else ∑ j ∈ Finset.Icc 1 (min D n),
      (Real.sqrt Q.η * ((j - 1).factorial : ℝ)⁻¹) • iteratedDeriv (j - 1)
        (fun ε => sourceFlux Q.edge Q.η ε t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) k X z) 0) =
      (if hh = 0 then 0 else ∑ j ∈ Finset.Icc 1 (min D n),
      (Real.sqrt Q.η * ((j - 1).factorial : ℝ)⁻¹) • iteratedDeriv (j - 1)
        (fun ε => sourceFlux Q.edge Q.η ε t
          (liftApply (n - j) (Dc (hh - 1) (n - j)) f t) k X z) 0) := by
    by_cases hhh : hh = 0
    · rw [ite_eq_left hhh, ite_eq_left hhh]
    · rw [ite_eq_right hhh, ite_eq_right hhh]
      apply Finset.sum_congr rfl
      intro j _
      have heps : (fun ε => sourceFlux Q.edge Q.η ε t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) k X z) =
          fun ε => sourceFlux Q.edge Q.η ε t
            (liftApply (n - j) (Dc (hh - 1) (n - j)) f t) k X z := by
        funext ε
        exact (hop (hh - 1) (n - j) (Or.inl (by omega))).sourceFlux hU Q.edge Q.η ε t k X hX z
      rw [heps]
  unfold liftFluxX
  rw [hS]
  simp only [ite_eq_left hn, h₁ X hX z, hf, hs]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVRegularity.Weighted
namespace AVRegularity.EntryWeakProofs

/-! The Fourier gradient and molecular flux have the literal H¹ derivative coordinates. -/

theorem molecularPlainGradient_coordinate (N K : ℕ) (c :
    CoupledPlainCoefficients (h := fun _ : Unit => ℂ) N) (k : Fin 2) :
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).compLpL
      2 (volume.restrict AVenhance.unitCube)
      ((coupledPlainGradientHk N c Unit.unit K).val (valueIndex2 K)) =
    cellDerivativeCLM k (coupledPlainSynthesis N Unit.unit 1 c) := by
  rw [coupledPlainGradientHk_jet_coordinate (h := fun _ : Unit => ℂ)
    N c Unit.unit K (valueIndex2 K) k]
  change (coupledPlainSynthesis N Unit.unit (K + 1) c).val
    ⟨⟨1, by omega⟩, Fin.snoc Fin.elim0 k⟩ =
    (coupledPlainSynthesis N Unit.unit 1 c).val ⟨⟨1, by decide⟩, fun _ => k⟩
  have hw : (Fin.snoc Fin.elim0 k : DerivativeWord2 1) = fun _ => k := by
    funext i
    fin_cases i
    rfl
  simp only [coupledPlainSynthesis_jet_eq_sum_modes, hw]

theorem molecularFlux_coordinate (G : Matrix (Fin 2) (Fin 2) ℝ)
    (w : Lp (PiLp 2 (fun _ : Fin 2 => ℂ)) 2 (volume.restrict AVenhance.unitCube))
    (k : Fin 2) :
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).compLpL
      2 (volume.restrict AVenhance.unitCube)
      ((metricFiberCoefficient (Matrix.transpose G)).compLpL
        2 (volume.restrict AVenhance.unitCube) w) =
    ∑ j : Fin 2, G j k • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
      2 (volume.restrict AVenhance.unitCube) w := by
  let p := fun j : Fin 2 => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
    2 (volume.restrict AVenhance.unitCube) w
  apply Lp.ext
  have hm := ContinuousLinearMap.coeFn_compLpL
    (metricFiberCoefficient (E := ℂ) (Matrix.transpose G)) w
  have hq := ContinuousLinearMap.coeFn_compLpL
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k)
    ((metricFiberCoefficient (E := ℂ) (Matrix.transpose G)).compLpL
      2 (volume.restrict AVenhance.unitCube) w)
  rw [Fin.sum_univ_two]
  filter_upwards [hm, hq, Lp.coeFn_add (G 0 k • p 0) (G 1 k • p 1),
    Lp.coeFn_smul (G 0 k) (p 0), Lp.coeFn_smul (G 1 k) (p 1),
    ContinuousLinearMap.coeFn_compLpL (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) 0) w,
    ContinuousLinearMap.coeFn_compLpL (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) 1) w]
    with x hmx hqx hax h0 h1 hp0 hp1
  rw [hqx]
  change ((metricFiberCoefficient (Matrix.transpose G)).compLpL
    2 (volume.restrict AVenhance.unitCube) w) x k = _
  rw [hmx, metricFiberCoefficient_apply]
  change (∑ j : Fin 2, G j k • w x j) = _
  rw [hax]
  simp only [Pi.add_apply, h0, h1, Pi.smul_apply, p, hp0, hp1, PiLp.proj_apply,
    Fin.sum_univ_two]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! In a real scalar field every real linear functional is a scalar multiple of identity. -/

theorem realFunctional_apply (ℓ : ℝ →L[ℝ] ℝ) (x : ℝ) : ℓ x = ℓ 1 * x := by
  have he := ℓ.map_smul x (1 : ℝ)
  simpa only [smul_eq_mul, mul_one, mul_comm] using he

theorem scalarFieldJet_eq (ℓ : ℝ →L[ℝ] ℝ) (c : ℝ → Vec 2 → ℝ) :
    cellJetOfField ℓ c = ℓ 1 • cellJetOfField (ContinuousLinearMap.id ℝ ℝ) c := by
  funext t a x
  simp only [cellJetOfField, Pi.smul_apply]
  split_ifs <;> rw [realFunctional_apply] <;> simp [Complex.real_smul]

theorem scalarFieldInverse_of_id {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ) (c₀ : Vec 2 → ℝ) (g c : ℝ → Vec 2 → ℝ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (r : ℕ∞) (c t))
    (hD : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩
      (fun t x => (g t x : ℂ)) (fun _ _ => 0)
      (cellJetOfField (ContinuousLinearMap.id ℝ ℝ) c))
    (hm : ∀ t ∈ Icc a b, cellMean
      (cellValue (cellJetOfField (ContinuousLinearMap.id ℝ ℝ) c) t) = 0)
    (hi : cellValue (cellJetOfField (ContinuousLinearMap.id ℝ ℝ) c) a =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => (c₀ x : ℂ)) :
    IsCellFieldInverse G v r a b c₀ g c := by
  refine ⟨hc, fun ℓ => ?_⟩
  have hs : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩
      (fun t x => (ℓ (g t x) : ℂ)) (fun _ _ => 0) (cellJetOfField ℓ c) := by
    rw [scalarFieldJet_eq]
    convert cellSolution_smul hD (ℓ 1) using 1
    · funext t x
      rw [realFunctional_apply]
      simp [Complex.real_smul]
    · funext t x
      simp
  refine ⟨hs, ?_, ?_, cellSolution_finite_energyNorm hab hs⟩
  · intro t ht
    rw [scalarFieldJet_eq]
    change (∫ x in AVenhance.unitCube, ℓ 1 •
      cellValue (cellJetOfField (ContinuousLinearMap.id ℝ ℝ) c) t x) = 0
    rw [integral_smul, ← cellMean, hm t ht, smul_zero]
  · rw [scalarFieldJet_eq]
    filter_upwards [hi] with x hx
    change ℓ 1 • cellValue (cellJetOfField (ContinuousLinearMap.id ℝ ℝ) c) a x = _
    rw [hx]
    rw [realFunctional_apply ℓ (c₀ x)]
    simp [Complex.real_smul]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! The actual weak construction has at most J times R edges in every inherited path. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakConstruction_rank_bounds (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (stage : ℕ → GenStage D hr Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage)
    (i : ℕ) (hi : M ≤ i) (hit : i ≤ M + J) :
    (∀ c ∈ (stage i).comps, weakComponentRank c ≤ (M + J - i) * Mn.R) ∧
    (∀ (v u : CompIn (stage i).comps), (stage i).fam.Γ v u →
      weakComponentRank u.1 < weakComponentRank v.1) := by
  have main : ∀ n, n ≤ J →
      (∀ c ∈ (stage (M + J - n)).comps, weakComponentRank c ≤ n * Mn.R) ∧
      (∀ (v u : CompIn (stage (M + J - n)).comps), (stage (M + J - n)).fam.Γ v u →
        weakComponentRank u.1 < weakComponentRank v.1) := by
    intro n
    induction n with
    | zero =>
        intro _
        obtain ⟨_, hcomps, he, _⟩ := hc.2.1
        constructor
        · intro c hmem
          have hmem' : c ∈ (stage (M + J)).comps := by simpa using hmem
          rw [hcomps, Finset.mem_singleton] at hmem'
          subst c
          simp [weakComponentRank]
        · intro v u γ
          let := he v u
          exact isEmptyElim γ
    | succ n ih =>
        intro hn
        obtain ⟨hcomp, he⟩ := ih (by omega)
        have hp := (hc.2.2 (M + J - n) (by omega) (by omega)).1
        have heq : M + J - n - 1 = M + J - (n + 1) := by omega
        constructor
        · have hb : ∀ c ∈ (stage (M + J - n - 1)).comps,
              weakComponentRank c ≤ n * Mn.R + Mn.R := by
            intro c hmem
            rw [hp.2.2.2.1] at hmem
            exact weakExtComps_rank_bound (stage (M + J - n)).level Mn.N Mn.R
              (n * Mn.R) (stage (M + J - n)).comps hcomp c hmem
          simpa only [heq, Nat.succ_mul, Nat.add_mul, one_mul] using hb
        · have hs := weakPassage_strict_rank P Mn rW
            (1 + (M + J - (M + J - n)) * Mn.N)
            (stage (M + J - n)) (stage (M + J - n - 1)) hp he
          exact Eq.mp (congrArg (fun l => ∀ (v u : CompIn (stage l).comps),
            (stage l).fam.Γ v u → weakComponentRank u.1 < weakComponentRank v.1) heq) hs
  have hn : M + J - i ≤ J := by omega
  have heq : M + J - (M + J - i) = i := by omega
  obtain ⟨hb, he⟩ := main (M + J - i) hn
  refine ⟨?_, ?_⟩
  · simpa only [heq] using hb
  · exact Eq.mp (congrArg (fun l => ∀ (v u : CompIn (stage l).comps),
      (stage l).fam.Γ v u → weakComponentRank u.1 < weakComponentRank v.1) heq) he

theorem weakConstruction_path_length_bound (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (stage : ℕ → GenStage D hr Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage)
    (i : ℕ) (hi : M ≤ i) (hit : i ≤ M + J) (h : ℕ) (π : StagePath (stage i) h) :
    h ≤ J * Mn.R := by
  obtain ⟨hb, he⟩ := weakConstruction_rank_bounds P Mn M J r rW stage hc i hi hit
  exact (stagePath_length_le_rank_bound (stage i) he ((M + J - i) * Mn.R) hb h π).trans
    (Nat.mul_le_mul_right Mn.R (by omega))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Finite-depth Jacobian production from primitive renewal-window estimates. -/

theorem finite_weak_chart_jets_of_small_windows (D : OCData) (s : ℝ)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ) (base J : ℕ) (hbase : 1 ≤ base)
    (Y : Vec 2) (p : ℕ → ℤ) (c : ℕ → ChainChild)
    (hp : ∀ n ≤ J, Odd (p n))
    (hs : ∀ n < J, IsScheduledIn D (base + 1 + n) (p (n + 1)) (p n))
    (K : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρe : ρ ≤ D.eps (base + J))
    (hprimitive : WeakPrimitiveChartSmall D base J 1) :
    ∀ n ≤ J, ∀ u r,
      |u - D.slotAnchor (base + 1 + n) (p n)| ≤
        finiteChainWindowRadius J n * ocTauPP D.α D.q D.Λ (base + 1 + n) →
      |r - D.slotAnchor (base + 1 + n) (p n)| ≤
        finiteChainWindowRadius J n * ocTauPP D.α D.q D.Λ (base + 1 + n) →
      ∀ a, 1 ≤ a → a ≤ K → ∀ x,
        ‖iteratedFDeriv ℝ a (rescaledChart ρ (fun y =>
          (finiteWeakChainGeom D base Y p c n).1 u y r)) x‖ ≤ weakChartJetBudget K n := by
  have hδp := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ := renewal_window_antitone (by linarith : D.α < 1) hδp.le hq.1 hΛ
  have heρ (m : ℕ) (hm : m ≤ base + J) : ρ ≤ D.eps m :=
    hρe.trans (EntryScales.epsilon_antitone hq.1 hΛ hm)
  intro n
  induction n with
  | zero =>
    intro _ u r hu hr a hapos haK x
    have h0 := (hprimitive (base + 1) le_rfl).1
    simp only [Nat.add_sub_cancel] at h0
    have htime : |u - r| ≤ 2 * (2 * (J : ℝ) + 1) * ocTauPP D.α D.q D.Λ (base + 1) := by
      have ht := abs_sub_le u (D.slotAnchor (base + 1) (p 0)) r
      have hr' := hr
      rw [abs_sub_comm r] at hr'
      change |u - D.slotAnchor (base + 1) (p 0)| ≤ (2 * (J : ℝ) + 1) * _ at hu
      change |D.slotAnchor (base + 1) (p 0) - r| ≤ (2 * (J : ℝ) + 1) * _ at hr'
      linarith
    have hb := scaled_coarse_flow_derivative_norm D s hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hseq
      base hbase r u (htime.trans h0) ρ hρ (heρ base (by omega)) 0 0 a hapos x
    have hb' : ‖iteratedFDeriv ℝ a (rescaledChart ρ (fun y => D.flowOf base u y r)) x‖ ≤
        (2 : ℝ) ^ a * (2 * a.factorial * (2 ^ 14 : ℝ) ^ (a - 1)) := by
      change ‖iteratedFDeriv ℝ a (fun z => ρ⁻¹ • D.flowOf base u (ρ • z) r) x‖ ≤ _
      simpa only [zero_add, sub_zero] using hb
    exact hb'.trans (weakBaseChartJetBudget_bounds_order K a haK)
  | succ n ih =>
    intro hn u r hu hr a ha' haK x
    let g := finiteWeakChainGeom D base Y p c n
    let h := ocTauPP D.α D.q D.Λ (base + 1 + n)
    let h' := ocTauPP D.α D.q D.Λ (base + 1 + (n + 1))
    let R := finiteChainWindowRadius J (n + 1)
    have hR : 0 ≤ R := finiteChainWindowRadius_nonneg _ _
    have hh : 0 ≤ h := (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ D.Λ)).le
    have hh' : h' ≤ h := hτ (by omega)
    have ha : |D.slotAnchor (base + 1 + (n + 1)) (p (n + 1)) - g.2.2| ≤ 2 * h := by
      have he := scheduled_anchor_distance D (by omega : 1 ≤ D.Λ) (base + 1 + n)
        (p (n + 1)) (p n) (hs n (by omega))
      rw [finiteWeakChainGeom_anchor] 
      have he' : |D.slotAnchor (base + 1 + (n + 1)) (p (n + 1)) -
          D.slotAnchor (base + 1 + n) (p n)| ≤ h' + h := by
        simpa only [h, h', Nat.add_assoc] using he
      exact he'.trans (by linarith)
    have hparent : ∀ u₀ r₀, |u₀ - g.2.2| ≤ (R + 2) * h →
        |r₀ - g.2.2| ≤ (R + 2) * h → ∀ a, 1 ≤ a → a ≤ K → ∀ x,
        ‖iteratedFDeriv ℝ a (rescaledChart ρ (fun y => g.1 u₀ y r₀)) x‖ ≤ weakChartJetBudget K n := by
      intro u₀ r₀ hu₀ hr₀ a ha haK x₀
      rw [finiteWeakChainGeom_anchor] at hu₀ hr₀
      rw [← finiteChainWindowRadius_succ J n hn] at hu₀ hr₀
      exact ih (by omega) u₀ r₀ hu₀ hr₀ a ha haK x₀
    have hsmall := primitive_shear_window_bound D (by omega : 1 ≤ D.Λ) base J hprimitive n
    have hb := child_window_positive_jet_bound_of_parent_bound D (by omega : 1 ≤ D.Λ) hζ
      (base + 1 + n) (p n) (hp n (by omega))
      (D.slotAnchor (base + 1 + (n + 1)) (p (n + 1))) (c n) g
      (finiteWeakChainGeom_smooth D base Y p c n) h h' R (weakChartJetBudget K n) ρ
      hh hh' hR (weakChartJetBudget_ge_one K n) hρ (heρ (base + 1 + n) (by omega))
      ha hsmall K hparent u r hu hr a ha' haK x
    exact hb

/-! Actual path data have at most one constituent per order and no constituent above the stage menu. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem pathEdges_nil_above_stage_order (G : GenStage D hr Dm bw j₀) (K : ℕ)
    (hK : G.maxOrderBound K) {h : ℕ} (π : StagePath G h)
    (p : OddSlot) (c : StageCtx D bw j₀ G.level p)
    (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (hd : K < d.val) :
    pathEdges G π p c v u d = [] := by
  unfold pathEdges
  by_cases hvu : v.val = u + 1 ∧ u.val < h
  · rw [dite_eq_left hvu]
    have hnot : ¬d.val ≤ (G.fam.identity _ _ (π.step ⟨u, hvu.2⟩).2.2).maxOrder := by
      have hb := hK _ _ (π.step ⟨u, hvu.2⟩).2.2
      omega
    rw [dite_eq_right hnot]
  · rw [dite_eq_right hvu]

theorem pathEdges_length_le_one (G : GenStage D hr Dm bw j₀) {h : ℕ} (π : StagePath G h)
    (p : OddSlot) (c : StageCtx D bw j₀ G.level p)
    (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) : (pathEdges G π p c v u d).length ≤ 1 := by
  unfold pathEdges
  split
  · split <;> simp only [List.length_cons, List.length_nil] <;> omega
  · simp only [List.length_nil, Nat.zero_le]

theorem weakFamilyPathEdges_nil_above_stage_order (G : GenStage D hr Dm bw j₀) (K : ℕ)
    (hK : G.maxOrderBound K) {h : ℕ} (π : StagePath G h)
    (p : OddSlot) (c : StageCtx D bw j₀ G.level p) (ρ : ℝ)
    (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (hd : K < d.val) :
    (familyLiftData D G.level p.1 c.1 ρ (pathEdges G π p c)).edge v u d = [] := by
  change (pathEdges G π p c v u d).map _ = []
  rw [pathEdges_nil_above_stage_order G K hK π p c v u d hd]
  rfl
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! The actual scheduled renewal windows supply the time-domain premises of mixed chart production. -/

def nativeWeakChartWindow (D : OCData) (base J : ℕ) (p : ℕ → ℤ) (n : ℕ) : Set ℝ :=
  {u | |u - D.slotAnchor (base + 1 + n) (p n)| ≤
    finiteChainWindowRadius J n * ocTauPP D.α D.q D.Λ (base + 1 + n)}

theorem nativeWeakChartWindow_anchor (D : OCData) (hΛ : 1 ≤ D.Λ)
    (base J : ℕ) (p : ℕ → ℤ) (n : ℕ) :
    D.slotAnchor (base + 1 + n) (p n) ∈ nativeWeakChartWindow D base J p n := by
  change |(_ : ℝ) - _| ≤ _
  rw [sub_self, abs_zero]
  exact mul_nonneg (finiteChainWindowRadius_nonneg J n) (Construction.Stream.ocTauPP_pos hΛ).le

theorem nativeWeakChartWindow_subset_parent (D : OCData) (hΛ : 1 ≤ D.Λ)
    (base J : ℕ) (p : ℕ → ℤ) (n : ℕ) (hn : n + 1 ≤ J)
    (hτ : ocTauPP D.α D.q D.Λ (base + 1 + (n + 1)) ≤ ocTauPP D.α D.q D.Λ (base + 1 + n))
    (hs : IsScheduledIn D (base + 1 + n) (p (n + 1)) (p n)) :
    nativeWeakChartWindow D base J p (n + 1) ⊆ nativeWeakChartWindow D base J p n := by
  have ha : |D.slotAnchor (base + 1 + (n + 1)) (p (n + 1)) -
      D.slotAnchor (base + 1 + n) (p n)| ≤ 2 * ocTauPP D.α D.q D.Λ (base + 1 + n) := by
    have hh := scheduled_anchor_distance D hΛ (base + 1 + n) (p (n + 1)) (p n) hs
    have hh' : |D.slotAnchor (base + 1 + (n + 1)) (p (n + 1)) -
      D.slotAnchor (base + 1 + n) (p n)| ≤
      ocTauPP D.α D.q D.Λ (base + 1 + (n + 1)) + ocTauPP D.α D.q D.Λ (base + 1 + n) := by
      simpa only [Nat.add_assoc] using hh
    exact hh'.trans (by linarith only [hτ])
  intro u hu
  have hb := child_window_parent_distance (finiteChainWindowRadius_nonneg J (n + 1)) hτ ha hu
  change |u - D.slotAnchor (base + 1 + n) (p n)| ≤ _
  rw [finiteChainWindowRadius_succ J n hn]
  exact hb

theorem nativeWeakChartWindow_shear_small (D : OCData) (hΛ : 1 ≤ D.Λ)
    (base J : ℕ) (p : ℕ → ℤ) (hprimitive : WeakPrimitiveChartSmall D base J 1)
    (n : ℕ) (u : ℝ) (hu : u ∈ nativeWeakChartWindow D base J p (n + 1)) :
    |u - D.slotAnchor (base + 1 + (n + 1)) (p (n + 1))| *
      ocA D.α D.q D.Λ (base + 1 + n) ≤ 1 := by
  have hA : 0 ≤ ocA D.α D.q D.Λ (base + 1 + n) := by
    unfold ocA
    exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  have hb := mul_le_mul_of_nonneg_right hu hA
  apply hb.trans
  apply le_trans ?_ (primitive_shear_window_bound D hΛ base J hprimitive n)
  have hR := finiteChainWindowRadius_nonneg J (n + 1)
  have ht := (Construction.Stream.ocTauPP_pos (α := D.α) (q := D.q) hΛ (m := base + 1 + (n + 1))).le
  exact mul_le_mul_of_nonneg_right (by nlinarith only [mul_nonneg hR ht]) hA

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The literal inherited source admits componentwise reserves throughout its outer divergence. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedSourceComponentArrayReserve (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ)) (η : ℝ) (A : Vec 2 →L[ℝ] ℝ)
    (f : ℝ → Vec 2 → Vec 2 → ι → ℝ)
    (Qf : ∀ u, JointSourceReserve (H + 1 + D) (fun t z Y => f t z Y u))
    (Qedge : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      JointSourceReserve (H + 1) (fun t z Y => γ.coeff α t Y z)) (j : ℕ) (v : ι) :
    JointSourceReserve H (fun t z Y => (Real.exp (A Y))⁻¹ •
      sourceComponentCoefficientArray edge η t
        (fun X y => Real.exp (A X) • f t y X) j v Y z) := by
  let P := fun k i t => sourceFluxComponentCoefficient edge η t
    (fun X y => Real.exp (A X) • f t y X) k i v
  let QP := fun (k : Fin 2) i =>
    normalizedSourceFluxComponentReserve (H + 1) edge η A f Qf Qedge k i v
  let F := fun k t z Y => (Real.exp (A Y))⁻¹ •
    covariantCoefficientStep η k (fun i => P k i t) j Y z
  have he : (fun t z Y => (Real.exp (A Y))⁻¹ •
      sourceComponentCoefficientArray edge η t
        (fun X y => Real.exp (A X) • f t y X) j v Y z) =
      fun t z Y => ∑ k : Fin 2, F k t z Y := by
    funext t z Y
    simp only [sourceComponentCoefficientArray, Finset.smul_sum, F, P]
  rw [he]
  exact JointSourceReserve.fintypeSum H F
    (fun k => normalizedCovariantStepReserve H A η (P k) k j (QP k))

def normalizedSourceComponentCoefficientReserve (H : ℕ) (hH : 1 ≤ H)
    (edge : ConstituentEdges D (fun _ : ι => ℝ)) (hD : 1 ≤ D)
    (η : ℝ) (A : Vec 2 →L[ℝ] ℝ) (f : ℝ → Vec 2 → Vec 2 → ι → ℝ)
    (Qf : ∀ u, JointSourceReserve (H + 1 + D) (fun t z Y => f t z Y u))
    (Qedge : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      JointSourceReserve (H + 1) (fun t z Y => γ.coeff α t Y z))
    (j : ℕ) (hj : j ≤ D) (v : ι) :
    JointSourceReserve H (fun t z Y => (Real.exp (A Y))⁻¹ •
      sourceCoeff edge η j t (fun X y => Real.exp (A X) • f t y X) Y z v) := by
  let Qwhole := jointSourcePiReserve (H + 1 + D) (fun u t z Y => f t z Y u) Qf
  have he (t : ℝ) : (fun Y z => sourceCoeff edge η j t
      (fun X y => Real.exp (A X) • f t y X) Y z v) =
      sourceComponentCoefficientArray edge η t
        (fun X y => Real.exp (A X) • f t y X) j v := by
    rw [sourceCoeff_eq_sourceCoefficientArray edge hD η t _
      ((Qwhole.exponentialGoodField A t).mono (by omega))
      (fun v u d γ hγ α => ((Qedge v u d γ hγ α).goodField t).mono (by omega))]
    apply sourceCoefficientArray_component_eq edge hD η t _ j hj
    · intro v u d γ hγ α
      apply Weighted.isBoxSmooth_of_joint_contDiff
      exact (((Qedge v u d γ hγ α).goodField t).mono (by omega : 1 + 1 ≤ H + 1)).1
    · apply Weighted.isBoxSmooth_of_joint_contDiff
      exact ((Qwhole.exponentialGoodField A t).mono
        (by omega : j + (D - j) ≤ H + 1 + D)).1
  have hfun : (fun t z Y => (Real.exp (A Y))⁻¹ •
      sourceCoeff edge η j t (fun X y => Real.exp (A X) • f t y X) Y z v) =
      fun t z Y => (Real.exp (A Y))⁻¹ • sourceComponentCoefficientArray edge η t
        (fun X y => Real.exp (A X) • f t y X) j v Y z := by
    funext t z Y
    rw [congrFun (congrFun (he t) Y) z]
  rw [hfun]
  exact normalizedSourceComponentArrayReserve H edge η A f Qf Qedge j v

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Centering an actual forcing retains its finite joint derivative budget. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def JointSourceReserve.center {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) :
    JointSourceReserve H (fun t z Y => f t z Y - fieldCellMean (fun x => f t x Y)) := by
  let L : E →L[ℝ] E := -ContinuousLinearMap.id ℝ E
  have he : (fun t z Y => f t z Y + L (fieldCellMean (fun x => f t x Y))) =
      fun t z Y => f t z Y - fieldCellMean (fun x => f t x Y) := by
    funext t z Y
    simp only [L, neg_apply, ContinuousLinearMap.id_apply, sub_eq_add_neg]
  exact (Q.add (Q.mean.map L)).congrSource he

theorem JointSourceReserve.center_budget {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (n : ℕ) :
    Q.center.budget n = (1 + ‖ContinuousLinearMap.id ℝ E‖ * 2 ^ n) * Q.budget n := by
  unfold JointSourceReserve.center
  rw [JointSourceReserve.congrSource_budget]
  change Q.budget n + ‖-ContinuousLinearMap.id ℝ E‖ * (2 ^ n * Q.budget n) = _
  rw [norm_neg]
  ring

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Physical path fluxes use only the local edge and coefficient germs and the metric at the readout point. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftFluxX_primitive_point_congr {U : Set (Vec 2)} (hU : IsOpen U)
    (Q Q' : LiftOperatorData ι h D) (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (hn : 2 ≤ n) (t : ℝ) (hΓ : SlowOpenEdgeEq U t Q.edge Q'.edge)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q, ∀ α X,
      X ∈ U → ∀ z v u, Cc p q m α t X z v u = Dc p q m α t X z v u)
    (X : Vec 2) (hX : X ∈ U) (hG : Q.G t X = Q'.G t X) (z : Vec 2) (k : Fin 2) :
    liftFluxX Q Cc f hh n t X z k = liftFluxX Q' Dc f hh n t X z k := by
  calc
    _ = liftFluxX Q Dc f hh n t X z k :=
      liftFluxX_slow_open_congr_predecessors hU Q Cc Dc f hh n hn t he X hX z k
    _ = liftFluxX {Q with edge := Q'.edge} Dc f hh n t X z k :=
      liftFluxX_edge_slow_open_congr hU Q Q'.edge Dc f hh n t hΓ k X hX z
    _ = _ := by
      unfold liftFluxX
      dsimp only
      rw [hη, hv, hG]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Literal inherited flux coefficients compose matrix grades, retaining path multiplicity and every edge amplitude. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def sourceFluxWordCount (D : ℕ) : ℕ :=
  ∑ d : Finset.Icc 2 D, Fintype.card (DerivativeWord2 (d.val - 1))

def normalizedSourceFluxMatrixBudget (H D L : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η BE BF : ℝ) : ℝ :=
  (L : ℝ) * (sourceFluxWordCount D : ℝ) * normalizedSourceFluxTermBudget H D A η BE BF

theorem normalizedSourceFluxMatrixBudget_nonneg (H D L : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BE BF : ℝ) (hBE : 0 ≤ BE) (hBF : 0 ≤ BF) :
    0 ≤ normalizedSourceFluxMatrixBudget H D L A η BE BF :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (normalizedSourceFluxTermBudget_nonneg H D A η BE BF hBE hBF)

end AVRegularity.EntryWeakProofs
end
end
