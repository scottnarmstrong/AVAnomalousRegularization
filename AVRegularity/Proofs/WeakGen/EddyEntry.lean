-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeakAssembly.NativeFamilyLiftUniqueness
public import AVRegularity.Proofs.WeakGen.Assembly.WeakRoute
public import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Proofs.CascadeInvariants.ReserveGrade
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
public import AVRegularity.Proofs.CascadeInvariants.PathFiner
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Proofs.GenSem.LiftOn.Omega

section
section
/-! Arbitrary finite reserves for weak-passage lifts, and uniqueness on their original windows.
The uniqueness theorem already permits different reserves; no reserve floor or weakening is needed.
Agreement is asserted on the grades constrained by the lift relation. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.WeakEntryProofs
open AVRegularity.WeakEntryProofs.Assembly AVRegularity.EntryWeakProofs
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.Providers.WeakGen

/-- Two inherited weak-source lifts agree on every grade constrained by their lift clauses,
even when their reserves differ. This applies in particular to the witnesses above and to
any witnesses of the outgoing passage. -/
theorem weakSource_highReserve_agrees {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    {G : GenStage D ScalarH Dm bw j₀} (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (s : WeakSource G) (R sX sZ N : ℕ) (ρ : ℝ)
    (Cc Dc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hc : s.IsLiftFamily R R N ρ Cc) (hd : s.IsLiftFamily sX sZ N ρ Dc)
    (k : ℤ) (A : RealChain) (hA : IsAdmissibleChain D bw j₀ G.level k A ∧ Odd k)
    (hs : ∀ v w n, s ≠ .eddy v w n) :
    ∀ hh, hh ≤ s.pathLen → ∀ n m (α : DerivativeWord2 m) τ,
      τ ∈ Set.Icc (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) →
      ∀ X ∈ ladderOmega D bw j₀ G.level k A ρ, ∀ z v u,
        Cc k A hh n m α τ X z v u = Dc k A hh n m α τ X z v u := by
  cases s with
  | eddy v w n => exact (hs v w n rfl).elim
  | inherited w h π n =>
    exact native_family_lift_coefficients_unique D hζ G.level k hA.2 A ρ _ _
      (GenSem.isOpen_ladderOmega _ _ _ _ _ _ _) _ _
      (weakData_lift_window D hΛ hζ hband G.level k) N h R R sX sZ
      (Cc k A) (Dc k A) (hc k A hA) (hd k A hA)

/-- The diagonal grade-zero lifts agree on the full slow space throughout their original
window, at every coefficient order, with no relation between their finite reserves. -/
theorem weakEddy_highReserve_agrees {D : OCData} {Dm : ℕ} (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (i : ℕ) (k : ℤ) (hk : Odd k) (A : RealChain) (ρ : ℝ) (R sX sZ N : ℕ)
    (Cc Dc : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hc : IsLiftSequence (familyLiftData (Dm := Dm) D i k A ρ (fun _ _ _ => [])) R R
      (D.slotStart i k / D.cellScaleSq i)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i) / D.cellScaleSq i) N 0 Cc)
    (hd : IsLiftSequence (familyLiftData (Dm := Dm) D i k A ρ (fun _ _ _ => [])) sX sZ
      (D.slotStart i k / D.cellScaleSq i)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i) / D.cellScaleSq i) N 0 Dc) :
    ∀ n m (α : DerivativeWord2 m) τ,
      τ ∈ Set.Icc (D.slotStart i k / D.cellScaleSq i)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i) / D.cellScaleSq i) →
      ∀ X z v u, Cc 0 n m α τ X z v u = Dc 0 n m α τ X z v u := by
  intro n m α τ hτ X z v u
  exact native_family_lift_coefficients_unique D hζ i k hk A ρ _ Set.univ isOpen_univ _ _
    (weakData_lift_window D hΛ hζ hband i k) N 0 R R sX sZ Cc Dc
    (Uniqueness.IsLiftSequence.toOn hc Set.univ) (Uniqueness.IsLiftSequence.toOn hd Set.univ)
    0 le_rfl n m α τ hτ X (Set.mem_univ X) z v u

/-- High-reserve lifts of one passage, with agreement on the inherited grades and the
separate grade-zero array consumed by the weak ledger. -/
theorem weakHighReserveLifts {plan : WeakCoefficientPlan}
    (hLX : WeakPassageLiftsStatement plan) : WeakHighReserveLiftsStatement plan := by
  classical
  intro x hgen w R
  obtain ⟨Cc, hc⟩ := hLX ⟨x.inst, x.i, x.hi, x.hiJ, x.stage,
    x.pc.1, fun j hj hjJ => x.pc.2 j (by omega) hjJ⟩ hgen R
  have hΛ : 1 ≤ x.inst.D.Λ := by
    rw [x.inst.hΛ]
    exact (by decide : 1 ≤ 128).trans ((plan.baseThreshold_ge _).trans x.inst.base_large)
  have hζ : IsFastProfile x.inst.D.ζ := by rw [x.inst.hζ]; exact x.inst.base.hζ
  have hband : IsOCBandChain x.inst.D.α x.inst.D.q x.inst.D.Λ x.inst.D.ζ
      x.inst.D.term x.inst.D.κ := by
    rw [x.inst.hα, x.inst.hq, x.inst.hΛ, x.inst.hζ, x.inst.term]
    exact x.inst.band
  have hDm : 1 ≤ x.inst.Dm := (Nat.le_add_right 1 _).trans x.inst.order
  let Cc' := fun (s : WeakSource (x.stage x.i)) (k : ℤ) (A : RealChain) =>
    if Odd k then Cc s k A else w.Cc s k A
  let Cc0 := nativeWeakEddyLiftFamily x.inst.D x.inst.Dm x.inst.physical.bw x.inst.j₀
    (x.stage x.i).level hΛ hζ hband x.inst.physical.Nw
  have hc0 k A hk hA := native_weak_eddy_lift_family x.inst.D x.inst.Dm hDm
    x.inst.physical.bw x.inst.j₀ (x.stage x.i).level hΛ hζ hband x.inst.physical.Nw
    R R k A hk hA
  refine ⟨Cc', Cc0, ?_, hc0, ?_, ?_⟩
  · intro s
    cases s with
    | eddy v u n => trivial
    | inherited v h π n =>
      intro k A hA
      simpa only [Cc', ite_eq_left hA.2] using hc (.inherited v h π n) k A hA
  · intro s hs k A hA τ hτ X hX hh hhH n m α z v u
    dsimp only [Cc']
    by_cases hk : Odd k
    · rw [ite_eq_left hk]
      exact weakSource_highReserve_agrees hζ hΛ hband s R x.inst.request.sX
        x.inst.request.sZ x.inst.physical.Nw (x.inst.D.eps ((x.stage x.i).level - 1))
        (Cc s) (w.Cc s) (hc s) (w.lifts s) k A ⟨hA, hk⟩
        (by intro v u n he; simp only [he, WeakSource.IsInherited] at hs)
        hh hhH n m α τ hτ X hX z v u
    · rw [ite_eq_right hk]
  · intro k A hk hA τ hτ n m α X z v u
    exact weakEddy_highReserve_agrees hζ hΛ hband (x.stage x.i).level k hk A
      (x.inst.D.eps ((x.stage x.i).level - 1)) R x.inst.request.sX x.inst.request.sZ
      x.inst.physical.Nw (Cc0 k A) (w.Cc0 k A) (hc0 k A hk hA) (w.lifts0 k A hk hA)
      n m α τ hτ X z v u

end AVRegularity.Providers.WeakGen
end
end

section
/-! A weak passage exists from its incoming holomorphic stage. Localized inherited lifts
are selected at phase representatives; the structural successor supplies the passage and tags. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.WeakEntryProofs AVRegularity.WeakEntryProofs.Assembly
namespace AVRegularity.Providers.WeakGen

/-- The qualitative passage needs only a level threshold above the carrier start. -/
def WeakExistsPlanOK (plan : WeakCoefficientPlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakCoefficientRequest A) (j₀ : ℕ), j₀ + 2 ≤ plan.levelThreshold R j₀

/-- Build one passage using arbitrary-reserve lifts and the existing structural successor. -/
theorem weakPassageExists {plan : WeakCoefficientPlan} (hplan : WeakExistsPlanOK plan)
    (hLX : WeakPassageLiftsStatement plan) : WeakPassageExistsStatement plan := by
  classical
  intro y hgen
  let x := y.inst
  let G := y.stage y.i
  let J := x.M + x.physical.Jw - y.i
  let Din := 1 + J * x.menu.N
  let H := J * x.menu.R
  have hyi : x.M < y.i := y.hi
  have hyJ : y.i ≤ x.M + x.physical.Jw := y.hiJ
  have htop : y.i + J = x.M + x.physical.Jw := by dsimp only [J]; omega
  have hc : IsWeakConstruction x.D x.P x.menu y.i J
      (x.D.termRW x.physical.σw x.M) 0 y.stage := by
    refine ⟨htop.symm, ?_, ?_⟩
    · rw [htop]; exact y.pc.1
    · intro i hi hiJ
      rw [htop] at hiJ
      have hp := y.pc.2 i hi hiJ
      rw [htop]
      exact hp
  have hlev : G.level = y.i := y.pc.level y.i le_rfl y.hiJ
  have hthr := hplan x.request x.j₀
  have hlarge := x.level_large
  have hi : 1 ≤ G.level - 1 := by rw [hlev]; omega
  have hj : x.j₀ ≤ G.level - 1 := by rw [hlev]; omega
  have hterm : x.D.term < G.level := by rw [hlev, x.term]; exact y.hi
  have ht : G.HasTags x.P :=
    weakConstruction_stage_hasTags x.P x.menu y.i J 0 _ hc y.i le_rfl (by omega)
  have horder : G.maxOrderBound Din :=
    weakConstruction_stage_maxOrderBound x.P x.menu y.i J 0 _ hc y.i le_rfl (by omega)
  have hpath : ∀ h, StagePath G h → h ≤ H :=
    weakConstruction_path_length_bound x.P x.menu y.i J 0 _ y.stage hc y.i le_rfl (by omega)
  have hDin : 1 ≤ Din := Nat.le_add_right 1 _
  have hDm : x.menu.N + Din ≤ x.Dm := by
    have hJ : J + 1 ≤ x.physical.Jw := by dsimp only [J]; omega
    have hm := Nat.mul_le_mul_right x.physical.Nw hJ
    have ho := x.order
    change x.physical.Nw + (1 + J * x.physical.Nw) ≤ x.Dm
    rw [Nat.add_mul, one_mul] at hm
    omega
  have hDm1 : 1 ≤ x.Dm := hDin.trans ((Nat.le_add_left Din x.menu.N).trans hDm)
  have hΛ : 1 ≤ x.D.Λ := by rw [x.hΛ]; exact (by have := case_Lambda_ge x; omega)
  have hζ : IsFastProfile x.D.ζ := by rw [x.hζ]; exact x.base.hζ
  have hband : IsOCBandChain x.D.α x.D.q x.D.Λ x.D.ζ x.D.term x.D.κ := by
    rw [x.hα, x.hq, x.hΛ, x.hζ, x.term]; exact x.band
  have heps : ∀ i, 0 < x.D.eps i := fun _ => Construction.Stream.ocEpsilon_pos hΛ
  have hrW : 0 < x.D.termRW x.physical.σw x.M := Real.rpow_pos_of_pos (heps _) _
  have hτ : 0 < ocTau x.D.α x.D.q x.D.Λ (G.level - 1) := Construction.Stream.ocTau_pos hΛ
  obtain ⟨Cc, hCc⟩ := hLX y hgen (max x.menu.sX x.menu.sZ)
  let C := phaseNormalizedLifts Cc
  let C0 := nativeWeakEddyLiftFamily x.D x.Dm x.physical.bw x.j₀ G.level hΛ hζ hband x.menu.N
  have hC : ∀ s : WeakSource G,
      s.IsLiftFamily x.menu.sX x.menu.sZ x.menu.N (x.D.eps (G.level - 1)) (C s) := by
    have hh := phaseNormalizedLifts_isLiftFamily hΛ hζ hband x.physical.bw_pos hgen
      (max x.menu.sX x.menu.sZ) (max x.menu.sX x.menu.sZ) x.menu.N
      (x.D.eps (G.level - 1)) Cc hCc
    intro s
    cases s with
    | eddy v w n => trivial
    | inherited w h π n =>
      intro k A hA
      exact liftSequenceOn_order_mono _ _ (le_max_left _ _) (le_max_right _ _) _ _ _ _ _
        (hh (.inherited w h π n) k A hA)
  have hC0 := native_weak_eddy_lift_family x.D x.Dm hDm1 x.physical.bw x.j₀ G.level
    hΛ hζ hband x.menu.N x.menu.sX x.menu.sZ
  have hperiodic : ∀ (p : OddSlot) (c : StageCtx x.D x.physical.bw x.j₀ (G.level - 1) p)
      (s : WeakSource G), s.Valid x.menu.N x.menu.R Din → ∀ d I t X,
      AVenhance.IsZ2Periodic (weakSourceTransferredFlux G x.menu.η0 C C0 p c s d I t X) := by
    intro p c s _hs d I t X
    exact phaseNormalized_transferred_flux_periodic G x.menu.N hΛ hζ hband
      x.physical.bw_pos hgen (by omega) Cc x.menu.η0 p c s d I t X
  refine ⟨weakSuccessorStageOfPeriodicTransfer G x.P ht x.menu Din H hDin hDm hpath
    (x.D.termRW x.physical.σw x.M) hrW heps hi hj hτ C C0 hperiodic, ?_, ?_⟩
  · exact weakSuccessorStage_isWeakPassage G x.P ht x.menu Din H hDin hDm hpath
      (x.D.termRW x.physical.σw x.M) hrW heps hi hj hτ C C0 hperiodic hterm horder hC hC0
  · exact weakSuccessorStage_hasTags G x.P ht x.menu Din H hDin hDm hpath
      (x.D.termRW x.physical.σw x.M) hrW heps hi hj hτ C C0 hperiodic

end AVRegularity.Providers.WeakGen
end
end

section
/-! Arbitrary finite reserves for one weak passage. Time-uniform holomorphic local bounds
produce local edge models; the existing native full-lift theorem patches them on the carrier. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.WeakEntryProofs AVRegularity.WeakEntryProofs.Assembly
namespace AVRegularity.Providers.WeakGen

/-- The qualitative lift construction needs only the lower base floor. No additional
carrier constant or level threshold is required beyond those in a weak coefficient plan. -/
def WeakLiftsPlanOK (plan : WeakCoefficientPlan) : Prop :=
  ∀ B : WeakCoefficientBase, 1 ≤ plan.baseThreshold B

/-- Lift families of every finite reserve on the incoming passage's admissible carrier. -/
theorem weakPassageLifts {plan : WeakCoefficientPlan} (hplan : WeakLiftsPlanOK plan) :
    WeakPassageLiftsStatement plan := by
  classical
  intro y hgen R
  have hΛ : 1 ≤ y.inst.D.Λ := by
    rw [y.inst.hΛ]
    exact (hplan y.inst.base).trans y.inst.base_large
  have hζ : IsFastProfile y.inst.D.ζ := by rw [y.inst.hζ]; exact y.inst.base.hζ
  have hband : IsOCBandChain y.inst.D.α y.inst.D.q y.inst.D.Λ y.inst.D.ζ
      y.inst.D.term y.inst.D.κ := by
    rw [y.inst.hα, y.inst.hq, y.inst.hΛ, y.inst.hζ, y.inst.term]
    exact y.inst.band
  have hDm : 1 ≤ y.inst.Dm := (Nat.le_add_right 1 _).trans y.inst.order
  refine ⟨nativeWeakSourceLiftFamily hΛ hζ hband y.inst.physical.Nw, ?_⟩
  intro s
  cases s with
  | eddy v u n => trivial
  | inherited w h π n =>
    dsimp only [WeakSource.IsLiftFamily, WeakSource.pathLen, nativeWeakSourceLiftFamily]
    intro k A hA
    simp only [nativeWeakPathLiftFamily, dite_eq_left hA]
    exact native_full_lift_all_orders y.inst.D hζ hΛ (y.stage y.i).level
      (weakData_kap_pos y.inst.D hΛ hζ hband (y.stage y.i).level) k hA.2 A hA.1.2.2.1
      (y.inst.D.eps ((y.stage y.i).level - 1))
      (pathEdges (y.stage y.i) π ⟨k, hA.2⟩ ⟨A, hA.1⟩) _ _
      (weakData_lift_window_strict y.inst.D hΛ hζ hband (y.stage y.i).level k)
      y.inst.physical.Nw h hDm _
      (GenSem.isOpen_ladderOmega _ _ _ _ _ _ _)
      (weak_path_local_reserves hΛ hζ hband y.inst.physical.bw_pos (y.stage y.i)
        hgen π k hA.2 _ A hA.1) R R

end AVRegularity.Providers.WeakGen
end
end
end

section
section
/-! **The constants of the inherited weak ledger** (weak entry). Every constant depends
on the request only (with its physical choices and base), never on the stage cap `Dm`, the level
`M` or the passage:
* the Péclet numbers of the weak levels are at most `weakPeBound B` (`weakCd_le`, from
  `EntryScales.weak_scales_core`: `ε_i^{1+α}/κ_M ≤ C ε_{i-1}^{(q+2)γ} ≤ C`);
* the letter profiles are those of the carrier calculus with that drift constant (`inhKappa`), which bound the
  profiles of every passage (`ledgerConsts_drift_mono`);
* the ledger constants (`LedgerConsts`, `exists_ledgerConsts`) at the cap
  `N₀ = 1 + J_wN_w`, the weight bound `L_* + J_w(4N₀ + 4)` and the reserve step `1/(J_wN₀)`
  (`inhData`);
* the constant map `Kinh`: `4^{N₀}(N₀+1) c^{N₀} W_r K W F_max · N₀^H max(1, 2^{N₀}C)^H`, with
  `H = J_wR_w` the path length bound and `F_max` the largest slow-flux constant of the ledger.
The plan condition `WeakInhPlanOK` asks the weight `L_*` of the plan to cover the fast weight of the
lifts, `liftWt N₀ H N₀`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
open scoped ENNReal NNReal

namespace AVRegularity.Providers.WeakGen

open CascadeInvariants Majorant

/-- The Péclet bound of the weak levels of a base. -/
def weakPeBound (B : WeakCoefficientBase) : ℝ :=
  Classical.choose (EntryScales.weak_scales_core B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq)

theorem one_le_weakPeBound (B : WeakCoefficientBase) : 1 ≤ weakPeBound B :=
  (Classical.choose_spec (EntryScales.weak_scales_core B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq)).1

variable {plan : WeakCoefficientPlan}

/-- **The Péclet number of a weak level is at most the bound of the base.** -/
theorem weakCd_le (x : WeakCoefficientInstance plan) {i : ℕ} (hi : x.M < i) :
    weakCd x i ≤ weakPeBound x.base := by
  have hspec := ((Classical.choose_spec (EntryScales.weak_scales_core x.base.hα₀ x.base.hα₁
    x.base.hs₀ x.base.hs₁ x.base.hq)).2 x.physical.Λ (case_Lambda_ge x) x.M (x.D.κ x.M)
    x.band.1 i hi).1
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.hΛ]; have := case_Lambda_ge x; omega
  have hζ : IsFastProfile x.D.ζ := by rw [x.hζ]; exact x.base.hζ
  have hband : IsOCBandChain x.D.α x.D.q x.D.Λ x.D.ζ x.D.term x.D.κ := by
    rw [x.hα, x.hq, x.hΛ, x.hζ, x.term]; exact x.band
  have hκ : 0 < x.D.κ x.M := by
    have := EntryWeakProofs.weakData_kap_pos x.D hΛ1 hζ hband x.M
    rwa [EntryWeakProofs.weakData_kap_terminal x.D x.M (by rw [x.term]), x.term] at this
  have hkap : ∀ j, x.M ≤ j → x.D.kap j = x.D.κ x.M := fun j hj => by
    rw [EntryWeakProofs.weakData_kap_terminal x.D j (by rw [x.term]; exact hj), x.term]
  have hsq : Real.sqrt (x.D.kap i * x.D.kap (i - 1)) = x.D.κ x.M := by
    rw [hkap i hi.le, hkap (i - 1) (by omega), Real.sqrt_mul_self hκ.le]
  have hγ := (Scales.admissible_exponent_facts x.base.hα₀ x.base.hα₁ x.base.hs₀ x.base.hs₁
    x.base.hq).1
  have hq1 : 1 < x.base.q := x.base.hq.1
  have hexp : 0 ≤ (x.base.q + 2) * ocGamma x.base.α x.base.q := by
    have : 0 ≤ x.base.q + 2 := by linarith
    positivity
  have hε1 : ocEpsilon x.base.q x.physical.Λ (i - 1) ^ ((x.base.q + 2) *
      ocGamma x.base.α x.base.q) ≤ 1 :=
    Real.rpow_le_one (Construction.Stream.ocEpsilon_pos (by have := case_Lambda_ge x; omega)).le
      (Applications.eps_le_one hq1 (case_Lambda_ge x)) hexp
  unfold weakCd
  rw [hsq]
  simp only [OCData.eps, x.hα, x.hq, x.hΛ]
  calc _ ≤ _ := hspec
    _ ≤ weakPeBound x.base * 1 :=
        mul_le_mul_of_nonneg_left hε1 (zero_le_one.trans (one_le_weakPeBound _))
    _ = _ := mul_one _

/-- The letter profiles of one passage are bounded by those of a larger drift constant. -/
theorem ledgerConsts_drift_mono {b Cd Cd' : ℝ} (hCd : Cd ≤ Cd') {Dm L : ℕ}
    {a Δ K W Cold Wr : ℝ} {S Kg Kd : ℝ≥0}
    (h : LedgerConsts b Dm L (ComplexContext.complexContextKappa b Cd') a Δ K W Cold Wr S Kg Kd) :
    LedgerConsts b Dm L (ComplexContext.complexContextKappa b Cd) a Δ K W Cold Wr S Kg Kd where
  ha3 := h.ha3
  hΔ := h.hΔ
  hK0 := h.hK0
  hW0 := h.hW0
  hC0 := h.hC0
  hWr0 := h.hWr0
  hK := h.hK
  hW := h.hW
  hCold := h.hCold
  hWr := h.hWr
  hKg := h.hKg
  hKd := fun k L' hL => (wsum_mono fun hh => by
    simp only [ComplexContext.complexContextKappa]
    split_ifs
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hCd Real.pi_pos.le)
    · exact le_rfl).trans (h.hKd k L' hL)
  hS := h.hS

/-- **The weight condition of the plan**: the weight `L_*` covers the fast weight of the lifts of
every inherited source. -/
def WeakInhPlanOK (plan : WeakCoefficientPlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakCoefficientRequest A),
    GenSem.UEnv.liftWt (1 + A.Jw * A.Nw) (A.Jw * A.Rw) (1 + A.Jw * A.Nw) ≤
      (plan.constants R).kW.Lstar

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}

/-- The weight bound of the weak stages. -/
def inhLmax (plan : WeakCoefficientPlan) (R : WeakCoefficientRequest A) : ℕ :=
  (plan.constants R).kW.Lstar + A.Jw * (4 * (1 + A.Jw * A.Nw) + 4)

/-- The reserve step of the inherited ledger. -/
def inhDelta (A : WeakCoefficientPhysical B) : ℝ := 1 / ((A.Jw : ℝ) * (1 + A.Jw * A.Nw : ℕ))

theorem inhDelta_pos (A : WeakCoefficientPhysical B) : 0 < inhDelta A := by
  have hJ : (0 : ℝ) < A.Jw := by exact_mod_cast A.Jw_pos
  have hN : (0 : ℝ) < ((1 + A.Jw * A.Nw : ℕ) : ℝ) := by
    have : 0 < 1 + A.Jw * A.Nw := by omega
    exact_mod_cast this
  unfold inhDelta
  positivity

/-- The letter profiles of the inherited ledger. -/
def inhKappa (B : WeakCoefficientBase) (A : WeakCoefficientPhysical B) : MajConsts :=
  ComplexContext.complexContextKappa A.bw (weakPeBound B)

/-- The constants of the ledger, as data. -/
structure InhLedgerData (b : ℝ) (Dm L : ℕ) (κc : MajConsts) (Δ : ℝ) where
  a : ℝ
  K : ℝ
  W : ℝ
  Cold : ℝ
  Wr : ℝ
  S : ℝ≥0
  Kg : ℝ≥0
  Kd : ℝ≥0
  h : LedgerConsts b Dm L κc a Δ K W Cold Wr S Kg Kd

theorem inhLedgerData_nonempty (plan : WeakCoefficientPlan) (R : WeakCoefficientRequest A) :
    Nonempty (InhLedgerData A.bw (1 + A.Jw * A.Nw) (inhLmax plan R) (inhKappa B A)
      (inhDelta A)) := by
  obtain ⟨a, K, W, Cold, Wr, S, Kg, Kd, h⟩ := exists_ledgerConsts A.bw_pos
    (ComplexContext.complexContextKappa_majOK (zero_le_one.trans (one_le_weakPeBound B))) (1 + A.Jw * A.Nw)
    (inhLmax plan R) (inhDelta_pos A)
  exact ⟨⟨a, K, W, Cold, Wr, S, Kg, Kd, h⟩⟩

/-- The chosen constants of the inherited ledger of a request. -/
def inhData (plan : WeakCoefficientPlan) (R : WeakCoefficientRequest A) :
    InhLedgerData A.bw (1 + A.Jw * A.Nw) (inhLmax plan R) (inhKappa B A) (inhDelta A) :=
  Classical.choice (inhLedgerData_nonempty plan R)

/-- **The constant map of the inherited ledger.** -/
def Kinh (plan : WeakCoefficientPlan) : WeakConstFn := fun {B} {A} R C =>
  4 ^ (1 + A.Jw * A.Nw) * (((1 + A.Jw * A.Nw : ℕ) : ℝ) + 1) *
    tConst (inhData plan R).K (inhData plan R).Cold (inhDelta A) ^ (1 + A.Jw * A.Nw) *
    ((inhData plan R).Wr * (inhData plan R).K * (inhData plan R).W *
      (fluxMax (inhKappa B A) (inhData plan R).S (inhData plan R).Kg (inhData plan R).Kd
        (1 + A.Jw * A.Nw) (A.Jw * A.Rw) (1 + A.Jw * A.Nw) : ℝ)) *
    (((1 + A.Jw * A.Nw : ℕ) : ℝ) ^ (A.Jw * A.Rw) * max 1 (2 ^ (1 + A.Jw * A.Nw) * C) ^ (A.Jw * A.Rw))

theorem Kinh_nonneg (plan : WeakCoefficientPlan) (R : WeakCoefficientRequest A) (C : ℝ) :
    0 ≤ Kinh plan R C := by
  have h := (inhData plan R).h
  have hc := tConst_nonneg h.hK0 h.hC0 h.hΔ
  have hm : 0 ≤ max 1 (2 ^ (1 + A.Jw * A.Nw) * C) := zero_le_one.trans (le_max_left _ _)
  have hW := h.hWr0
  have hK := h.hK0
  have hW' := h.hW0
  unfold Kinh
  positivity

end AVRegularity.Providers.WeakGen
end
end

section
/-! **The finer outputs of an inherited weak source** (weak entry, inherited ledger). Over the re-capped
incoming stage `G^♭ = G.recap N` with no export (`GenStage.recap`) and its old certificate, the
coefficients of the finer output of an inherited source (the path mean of degree `n ≤ N` along a
path `π`, with the lifts of the passage) are graded slot family functions with the size of the ledger
(`inheritedFine`). The path mean is computed with lifts of a high reserve `R ≥ 2N + 2`, which agree
with the lifts of the passage on the windows and the admissible offsets on the grades `≤ h`. The
proof combines the cut-off lift setup of the re-capped path family (the lifts restrict to the
cap, `isLiftSequenceOn_restrict`), the graded path mean (`slotFamRepP_pathMean_of_path`), the
cross-cap identity of the path means (`pathMeanFlux_restrict`), and the agreement of the two lift
families on the open set `ladderOmega ∋ 0` (`Uniqueness.pathMeanFlux_eq_of_agreeOn`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
open scoped ENNReal NNReal

namespace AVRegularity.Providers.WeakGen

open CascadeInvariants GenSem Majorant

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- A time of the output window, in cell time, lies in the lift window. -/
theorem inv_mul_mem_liftWindowOf {m : ℕ} {k : ℤ} (hc : 0 < D.cellScaleSq m) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) :
    (D.cellScaleSq m)⁻¹ * t ∈ liftWindowOf D m k := by
  obtain ⟨h1, h2⟩ := ht
  refine ⟨?_, ?_⟩
  · rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hc.le)
  · rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hc.le)

/-- **The finer outputs of an inherited source are graded slot family functions** over the old
certificate of the re-capped stage. -/
theorem inheritedFine (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκb : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b) (hεn : ∀ k, 0 ≤ D.eps k)
    (G : GenStage D ScalarH Dm b j₀) {N : ℕ}
    (hN : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).maxOrder ≤ N) (hND : N ≤ Dm)
    {μo : Comp → ℝ} {Lo : ℕ} {Co : ℝ}
    (hcert : (G.recap N hN noExports).OldCert noExports μo Lo Co)
    (hGen : (G.recap N hN noExports).IsGenerated) (hT : G.IsSlotTransverse)
    (wd : List WordLetter) {h : ℕ} (π : StagePath G h) (n : ℕ)
    (Cc Cc' : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) {R Nl : ℕ}
    (hlift : ∀ (k : ℤ) (A : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k),
      IsLiftSequenceOn (ladderOmega D b j₀ G.level k A (D.eps (G.level - 1)))
        (familyLiftData D G.level k A (D.eps (G.level - 1))
          (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩))
        R R (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Nl h
        (Cc' k A))
    (hagree : ∀ (k : ℤ) (A : RealChain), IsAdmissibleChain D b j₀ G.level k A →
      ∀ τ ∈ liftWindowOf D G.level k,
      ∀ X ∈ ladderOmega D b j₀ G.level k A (D.eps (G.level - 1)),
      ∀ hh ≤ h, ∀ n' m (α : DerivativeWord2 m) z v u,
        Cc' k A hh n' m α τ X z v u = Cc k A hh n' m α τ X z v u)
    (hNl : Nl ≤ N) (hNR : Nl + N + 2 ≤ R) (hn1 : 1 ≤ n) (hnN : n ≤ N) (hnR : n + N + 2 ≤ R)
    (κ : MajConsts) {Δ μ₀ : ℝ} {S Kg Kd : ℝ≥0} (hXok : (oldCtx hcert κ Δ μ₀ S Kg Kd).Ok)
    (hμ : ∀ j : Fin h, μ₀ ≤ μo (π.step j).1.1)
    (hSl : ENNReal.ofReal |D.eps (G.level - 1)| *
      (κ.Cslow / ENNReal.ofReal (D.eps (G.level - 1) * Δ)) ≤ S)
    (hη0 : 0 ≤ D.kap G.level / D.kap (G.level - 1))
    (hη1 : D.kap G.level / D.kap (G.level - 1) ≤ 1) (hL₀ : UEnv.liftWt N h Nl ≤ Lo)
    (hLn : UEnv.liftWt N h n ≤ Lo) (k : ℤ) (hk : Odd k) (d₁ : ℕ)
    (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2) :
    SlotFamRepP D b j₀ noExports G.level k (oldCtx hcert κ Δ μ₀ S Kg Kd) (fun t A =>
      fluxCoeff ((WeakSource.inherited wd h π n).fluxOp (D.eps (G.level - 1)) Cc Cc0 k t A)
        d₁ I₁ 0 i₀)
      (n - 1 - (d₁ - 1))
      (Real.toNNReal |LiftGenSetup.pathMeanPref D G.level (D.eps (G.level - 1)) n d₁| *
        (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) *
          (UEnv.fluxXc (oldCtx hcert κ Δ μ₀ S Kg Kd) N
            (liftB (oldCtx hcert κ Δ μ₀ S Kg Kd) N) h n *
            ∏ j : Fin h, edgeTheta hcert ((π.recap (N := N) (hN := hN) (𝒮 := noExports)).step j).1
              ((π.recap (N := N) (hN := hN) (𝒮 := noExports)).step j).2.1
              ((π.recap (N := N) (hN := hN) (𝒮 := noExports)).step j).2.2))) := by
  set ρ := D.eps (G.level - 1) with hρ
  have hε : ρ ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκb G.level
  have hTb : (G.recap N hN noExports).IsSlotTransverse := hT
  have hset : CutoffLiftSetup D b j₀ (G.recap N hN noExports).exports
      (G.recap N hN noExports).level k ρ
      (pathEdgesAt (G.recap N hN noExports) π.recap ⟨k, hk⟩) (Cc' k) R R Nl R :=
    cutoffLiftSetup_of_path hΛ hζ hκb (G.recap N hN noExports) hGen hTb π.recap k hk ρ
      (div_ne_zero hε hε) (Cc' k) le_rfl le_rfl hNR
      (fun A hA => isLiftSequenceOn_recap hND π ⟨k, hk⟩ ⟨A, hA⟩ k A ρ hNl (hlift k A ⟨hA, hk⟩))
      (fun A hA τ hτ v u d γ hγ α c => contDiffOn_liftedPathEdge hΛ hζ hκb hb
        (G.recap N hN noExports) hcert π.recap k hk ρ hA hτ v u d γ hγ α c R)
  have hPM := slotFamRepP_pathMean_of_path hΛ hζ hκb hb.le hεn hcert hTb π.recap k hk ρ
    (Cc' k) hset κ hXok hμ hSl hη0 hη1 hL₀ hn1 hLn hnR d₁ I₁ i₀
  refine hPM.congr fun A hA t ht => ?_
  rw [pathEdgesAt_of_admissible (G.recap N hN noExports) π.recap ⟨k, hk⟩ hA]
  have hfo : (WeakSource.inherited wd h π n).fluxOp ρ Cc Cc0 k t A =
      pathMeanFlux D G.level ρ (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩))
        (Cc k A) n t := by
    unfold WeakSource.fluxOp
    rw [dite_eq_left ⟨hA, hk⟩]
  rw [hfo]
  have hE : EdgesBelow N
      (familyLiftData (Dm := Dm) D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge :=
    edgesBelow_liftEdges (edgesBelow_pathEdges hN π ⟨k, hk⟩ ⟨A, hA⟩) _ _
  have key : pathMeanFlux D (G.recap N hN noExports).level ρ
      (familyLiftData D (G.recap N hN noExports).level k A ρ
        (pathEdges (G.recap N hN noExports) π.recap ⟨k, hk⟩ ⟨A, hA⟩)) (Cc' k A) n t =
      pathMeanFlux D G.level ρ (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩))
        (Cc' k A) n t :=
    (congrArg (fun Q => pathMeanFlux D G.level ρ Q (Cc' k A) n t)
      (familyLiftData_recap hND π ⟨k, hk⟩ ⟨A, hA⟩ k A ρ)).trans
      (pathMeanFlux_restrict hND D G.level ρ hE (Cc' k A) hnN t)
  refine (congrArg (fun L => fluxCoeff L d₁ I₁ 0 i₀) key).trans ?_
  unfold fluxCoeff
  rw [Uniqueness.pathMeanFlux_eq_of_agreeOn D G.level ρ _ (Cc' k A) (Cc k A) n t
    (isOpen_ladderOmega D b j₀ G.level k A ρ)
    (fun hh hle n' m' α X hX => funext fun z => funext fun v => funext fun u =>
      hagree k A hA _ (inv_mul_mem_liftWindowOf hc ht) X hX hh hle n' m' α z v u) _ 0
    (by rw [smul_zero]; exact zero_mem_ladderOmega hζ hA ρ)]

end AVRegularity.Providers.WeakGen
end
end

section
/-! **Weak entry, the entries of the inherited sources**
(`weakInheritedLedger`). An identity of the outgoing stage whose source is the inherited path mean
of degree `n` along a path `π` of `h` edges has its ledger entry at the constant `Kinh(C)`:
* its coefficient is the transfer of the path mean (`WeakPassageWitness.flux`). Over the old
  certificate of the incoming stage re-capped at `N₀ = 1 + J_wN_w` (`WeakCertified.recap_oldCert`,
  record factor `2^{N₀}C`), its finer outputs are graded slot family functions
  (`inheritedFine`, with the high-reserve lifts of `WeakHighReserveLiftsStatement`);
* the path-mean entry (`pathMean_ledger_entry`) gives the expressions, with no export and the
  certified leaves, and the bound `W_r pmBound(d)` of the weighted majorant sum, zero below the
  order `2`. Every drift letter of a context expression of level `i - 1` is at a level `≥ i`
  (`driftIn_ctx`);
* at a weak level `d_* = ε_i` and `ρ = ε_{i-1}`, so the tagged size `pmBound_record_le` is
  `4^{N₀}(N₀+1)c^{N₀} W_r K W (ε_i/ε_{i-1})^{n-2} F_P`, with
  `F_P ≤ F_max N₀^h (2^{N₀}C)^h ∏_j Θ̂_{π_j}` (`prod_edgeTheta_le`); the product of the incoming
  record sizes is the size of the identity and `ε_i` its length (`inherited_record`), and
  `h ≤ J_wR_w` (`pathLen_le`).
The plan conditions are those of the carrier calculus (`WeakComplexContextPlanOK`, for the carrier start) and the weight
condition `WeakInhPlanOK`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
open scoped ENNReal NNReal

namespace AVRegularity.Providers.WeakGen

open CascadeInvariants GenSem Majorant

/-- The algebra of the final bound. -/
theorem inh_bound {X Z WKW r FP fx FM P Nh NH Ch MH : ℝ} (hX : X ≤ Z * (WKW * r * FP))
    (hFP : FP ≤ fx * (Nh * (Ch * P))) (hfx : fx ≤ FM) (hNh : Nh ≤ NH) (hCh : Ch ≤ MH)
    (hZ : 0 ≤ Z) (hWKW : 0 ≤ WKW) (hr : 0 ≤ r) (hfx0 : 0 ≤ fx) (hNh0 : 0 ≤ Nh)
    (hCh0 : 0 ≤ Ch) (hP : 0 ≤ P) :
    X ≤ Z * (WKW * FM) * (NH * MH) * P * r := by
  have h1 : Ch * P ≤ MH * P := mul_le_mul_of_nonneg_right hCh hP
  have h2 : Nh * (Ch * P) ≤ NH * (MH * P) :=
    mul_le_mul hNh h1 (mul_nonneg hCh0 hP) (hNh0.trans hNh)
  have h3 : fx * (Nh * (Ch * P)) ≤ FM * (NH * (MH * P)) :=
    mul_le_mul hfx h2 (mul_nonneg hNh0 (mul_nonneg hCh0 hP)) (hfx0.trans hfx)
  have h4 : Z * (WKW * r * FP) ≤ Z * (WKW * r * (FM * (NH * (MH * P)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hFP.trans h3) (mul_nonneg hWKW hr)) hZ
  calc X ≤ _ := hX.trans h4
    _ = _ := by ring

/-- The bound of a transferred path mean vanishes above its maximal order. -/
theorem pmBound_eq_zero_of_lt (D : OCData) (i m : ℕ) (ρ : ℝ) (n : ℕ) {Dγ : ℕ} (K W c lam FP : ℝ)
    {d : ℕ} (hd : Dγ < d) : pmBound D i m ρ n Dγ K W c lam FP d = 0 := by
  unfold pmBound
  rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, mul_zero]

/-- **The tagged size of a path mean at `ℓ' = ρ = ε_i`**, for one coefficient. -/
theorem inh_pm_le (D : OCData) {i m n N : ℕ} {ρ K W c Wr FP : ℝ} (hnN : n ≤ N) (hK : 0 ≤ K)
    (hW : 0 ≤ W) (hc : 1 ≤ c) (hWr : 0 ≤ Wr) (hF : 0 ≤ FP) (hρ : 0 < ρ) (hκ : 0 < D.kap i)
    (hL : 0 < D.cellScaleSq m)
    (hD : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ 2 = D.kap i * D.cellScaleSq m)
    (hDst : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) (hρE : D.eps i = ρ) (hn : 2 ≤ n)
    {d : ℕ} (hd : 2 ≤ d) (hdN : d ≤ N) :
    Wr * pmBound D i m ρ n n K W c 1 FP d ≤
      4 ^ N * ((N : ℝ) + 1) * c ^ N *
        (Wr * K * W * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ (n - 2) * FP) := by
  have hE : 0 < D.eps i := hρE ▸ hρ
  have hR := pmBound_record_le D i m ρ (n := n) (Dγ := n) (Dm := N) hnN hK hW hc hWr hF hρ hκ
    hL hD hDst hE hρ hn d hd hdN (lam := 1) (Q := 1) zero_le_one
    (fun i' => by rw [hρE, div_self hρ.ne', one_pow, one_pow, one_mul])
  rw [hρE, div_self hρ.ne', one_pow, one_mul] at hR
  simp only [abs_one, mul_one] at hR
  have h0 : 0 ≤ Wr * pmBound D i m ρ n n K W c 1 FP d :=
    mul_nonneg hWr (pmBound_nonneg D i m ρ n n 1 hK hW (by linarith) hE.le hF d)
  refine le_trans ?_ hR
  refine (Finset.single_le_sum (f := fun _ : Fin 2 => Wr * pmBound D i m ρ n n K W c 1 FP d)
    (fun _ _ => h0) (Finset.mem_univ 0)).trans ?_
  exact Finset.single_le_sum (f := fun _ : DerivativeWord2 (d - 1) =>
      ∑ _c : Fin 2, Wr * pmBound D i m ρ n n K W c 1 FP d)
    (fun _ _ => Finset.sum_nonneg fun _ _ => h0) (Finset.mem_univ (fun _ => 0))

/-- **The bound of one coefficient of an inherited identity**, over the re-capped stage. -/
theorem inh_coeff_bound {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (D : OCData) {G : GenStage D ScalarH Dm b j₀}
    {N : ℕ} {hN : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).maxOrder ≤ N}
    {μo : Comp → ℝ} {Lo : ℕ} {Co : ℝ}
    (hcert : (G.recap N hN noExports).OldCert noExports μo Lo Co) {h : ℕ} (π : StagePath G h)
    (fx : ℝ≥0) {i n d H : ℕ} {ρ K W c Wr FM : ℝ} (hnN : n ≤ N) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hc : 1 ≤ c) (hWr : 0 ≤ Wr) (hρ : 0 < ρ) (hκ : 0 < D.kap i)
    (hL : 0 < D.cellScaleSq G.level)
    (hDst : ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) = D.eps G.level)
    (hD : ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) ^ 2 =
      D.kap i * D.cellScaleSq G.level)
    (hρE : D.eps i = ρ) (hn2 : 2 ≤ n) (hCo : 0 ≤ Co)
    (hℓ : ∀ j : Fin h, 3 ≤ (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).maxOrder →
      (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.length ≤ D.eps G.level)
    (hfx : (fx : ℝ) ≤ FM) (hhH : h ≤ H) (hN1 : 1 ≤ N) (hεG : 0 ≤ D.eps G.level)
    (hKc : 0 ≤ 4 ^ N * ((N : ℝ) + 1) * c ^ N * (Wr * K * W * FM) *
      ((N : ℝ) ^ H * max 1 Co ^ H)) :
    Wr * (if 2 ≤ d then pmBound D i G.level ρ n n K W c 1
        ((fx * ∏ j : Fin h, edgeTheta hcert ((π.recap (N := N) (hN := hN) (𝒮 := noExports)).step j).1
          ((π.recap (N := N) (hN := hN) (𝒮 := noExports)).step j).2.1
          ((π.recap (N := N) (hN := hN) (𝒮 := noExports)).step j).2.2 : ℝ≥0) : ℝ) d else 0) ≤
      4 ^ N * ((N : ℝ) + 1) * c ^ N * (Wr * K * W * FM) * ((N : ℝ) ^ H * max 1 Co ^ H) *
        (∏ j : Fin h, (G.fam.identity _ _ (π.step j).2.2).record.size) *
        (D.eps G.level / D.eps i) ^ (n - 2) := by
  have hP : 0 ≤ ∏ j : Fin h, (G.fam.identity _ _ (π.step j).2.2).record.size :=
    Finset.prod_nonneg fun j _ => (G.fam.identity _ _ (π.step j).2.2).record.size_nonneg
  have hE : 0 < D.eps i := hρE ▸ hρ
  have hratio : 0 ≤ (D.eps G.level / D.eps i) ^ (n - 2) := pow_nonneg (div_nonneg hεG hE.le) _
  have hRHS := mul_nonneg (mul_nonneg hKc hP) hratio
  split_ifs with hd2
  swap
  · rw [mul_zero]; exact hRHS
  by_cases hdN : d ≤ N
  swap
  · rw [pmBound_eq_zero_of_lt _ _ _ _ _ _ _ _ _ _ (by omega), mul_zero]; exact hRHS
  refine (inh_pm_le D hnN hK hW hc hWr (NNReal.coe_nonneg _) hρ hκ hL hD
    (by rw [hDst]; exact hεG) hρE hn2 hd2 hdN).trans ?_
  rw [hDst, ← hρE]
  have hprod := prod_edgeTheta_le hcert π.recap hCo hℓ
  have hFP := mul_le_mul_of_nonneg_left hprod (NNReal.coe_nonneg fx)
  rw [← NNReal.coe_mul] at hFP
  have hNh : (N : ℝ) ^ h ≤ (N : ℝ) ^ H := pow_le_pow_right₀ (by exact_mod_cast hN1) hhH
  have hCh : Co ^ h ≤ max 1 Co ^ H :=
    (pow_le_pow_left₀ hCo (le_max_right 1 _) h).trans (pow_le_pow_right₀ (le_max_left _ _) hhH)
  exact inh_bound le_rfl hFP hfx hNh hCh (by positivity) (mul_nonneg (mul_nonneg hWr hK) hW)
    hratio (NNReal.coe_nonneg _) (by positivity) (by positivity) hP

variable {plan : WeakCoefficientPlan}

/-- **The ledger entry of an inherited identity.** -/
theorem weakInherited_entry (hplan : WeakComplexContextPlanOK plan) (hLw : WeakInhPlanOK plan)
    (hHR : WeakHighReserveLiftsStatement plan) (x : WeakPassageAt plan) {C : ℝ} (hC : 0 ≤ C)
    (hW : WeakCertified C (weakReserve x.inst x.i) (weakWeight x.inst x.i) (x.stage x.i))
    (w : CaseWitness x) (v' u' : CompIn (x.stage (x.i - 1)).comps)
    (γ' : (x.stage (x.i - 1)).fam.Γ v' u') {wd : List WordLetter} {h : ℕ}
    {π : StagePath (x.stage x.i) h} {n : ℕ} (hs : (w.e v' u' γ').1 = .inherited wd h π n) :
    WeakLedgerEntry x (Kinh plan x.inst.request C) (weakReserve x.inst (x.i - 1))
      (weakWeight x.inst (x.i - 1)) v' u' γ' := by
  intro d I kk
  -- standing facts
  have hΛ : 128 ≤ x.inst.D.Λ := by rw [x.inst.hΛ]; exact case_Lambda_ge x.inst
  have hΛ1 : 1 ≤ x.inst.D.Λ := by omega
  have hζ : IsFastProfile x.inst.D.ζ := by rw [x.inst.hζ]; exact x.inst.base.hζ
  have hq : 1 < x.inst.D.q := by rw [x.inst.hq]; exact x.inst.base.hq.1
  have hκb : IsOCBandChain x.inst.D.α x.inst.D.q x.inst.D.Λ x.inst.D.ζ x.inst.D.term
      x.inst.D.κ := by
    rw [x.inst.hα, x.inst.hq, x.inst.hΛ, x.inst.hζ, x.inst.term]; exact x.inst.band
  have hb := x.inst.physical.bw_pos
  have hstart := (case_complexContextBase hplan x.inst 0).hstart
  have hεpos : ∀ k, 0 < x.inst.D.eps k := fun k => Construction.Stream.ocEpsilon_pos hΛ1
  have hεn : ∀ k, 0 ≤ x.inst.D.eps k := fun k => (hεpos k).le
  have hi := x.hi
  have hiJ := x.hiJ
  have hlevi : (x.stage x.i).level = x.i := x.pc.level x.i (by omega) hiJ
  have hlev' : (x.stage (x.i - 1)).level = x.i - 1 := x.pc.level (x.i - 1) le_rfl (by omega)
  have hκM : 0 < x.inst.D.κ x.inst.M := by
    have := EntryWeakProofs.weakData_kap_pos x.inst.D hΛ1 hζ hκb x.inst.M
    rwa [EntryWeakProofs.weakData_kap_terminal x.inst.D x.inst.M (by rw [x.inst.term]),
      x.inst.term] at this
  have hkap : ∀ j, x.inst.M ≤ j → x.inst.D.kap j = x.inst.D.κ x.inst.M := fun j hj => by
    rw [EntryWeakProofs.weakData_kap_terminal x.inst.D j (by rw [x.inst.term]; exact hj),
      x.inst.term]
  have hkapi : x.inst.D.kap (x.stage x.i).level = x.inst.D.κ x.inst.M := hkap _ (by omega)
  have hkapi' : x.inst.D.kap ((x.stage x.i).level - 1) = x.inst.D.κ x.inst.M :=
    hkap _ (by omega)
  have hkap' : x.inst.D.kap (x.stage (x.i - 1)).level = x.inst.D.κ x.inst.M := hkap _ (by omega)
  -- the source
  have hV := (w.e v' u' γ').2.1
  rw [hs] at hV
  obtain ⟨-, hh1, hn2, -⟩ := hV
  have hrec := x.inherited_record w v' u' γ' hs
  have hnN : n ≤ weakCap x.inst := by
    have := x.outgoing_maxOrder_le w v' u' γ'
    rwa [hrec.2.2] at this
  have hhH : h ≤ x.inst.physical.Jw * x.inst.physical.Rw := x.pathLen_le π
  -- the re-capped stages and the old certificate
  have hND : weakCap x.inst ≤ x.inst.Dm := x.inst.order
  have hN := x.incoming_maxOrder_le
  have hN' := x.outgoing_maxOrder_le w
  have hcert := hW.recap_oldCert (N := weakCap x.inst) (hN := hN) (𝒮 := noExports) hC
    (hεpos _) x.incoming_length_le
  have hGen := hW.weakHolGen.recap_isGenerated (weakCap x.inst) hN
  have hT := hW.weakHolGen.isSlotTransverse hΛ1 hζ hb hstart
  -- the lifts of a high reserve
  obtain ⟨Cc', -, hL', -, hAg, -⟩ := hHR x hW.weakHolGen w (2 * weakCap x.inst + 2)
  -- the constants
  have hLC : LedgerConsts x.inst.physical.bw (weakCap x.inst) (inhLmax plan x.inst.request)
      (weakKappa x.inst x.i) (inhData plan x.inst.request).a (inhDelta x.inst.physical)
      (inhData plan x.inst.request).K (inhData plan x.inst.request).W
      (inhData plan x.inst.request).Cold (inhData plan x.inst.request).Wr
      (inhData plan x.inst.request).S (inhData plan x.inst.request).Kg
      (inhData plan x.inst.request).Kd :=
    ledgerConsts_drift_mono (weakCd_le x.inst hi) (inhData plan x.inst.request).h
  have hJ : (0 : ℝ) < x.inst.physical.Jw := by exact_mod_cast x.inst.physical.Jw_pos
  have hres := weakReserve_mem x.inst hiJ
  have hres' := weakReserve_mem x.inst (i := x.i - 1) (by omega)
  have hstep : weakReserve x.inst x.i =
      weakReserve x.inst (x.i - 1) + 1 / x.inst.physical.Jw := by
    unfold weakReserve
    rw [show x.i - x.inst.M = (x.i - 1 - x.inst.M) + 1 by omega]
    push_cast
    ring
  have hNΔ : (weakCap x.inst : ℝ) * inhDelta x.inst.physical = 1 / x.inst.physical.Jw := by
    unfold inhDelta
    field_simp
  have hLo : weakWeight x.inst x.i ≤ inhLmax plan x.inst.request := by
    unfold weakWeight inhLmax
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hLn : weakWeight x.inst (x.i - 1) ≤ inhLmax plan x.inst.request := by
    unfold weakWeight inhLmax
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hLs : (plan.constants x.inst.request).kW.Lstar ≤ weakWeight x.inst x.i :=
    Nat.le_add_right _ _
  have hlw : UEnv.liftWt (weakCap x.inst) (x.inst.physical.Jw * x.inst.physical.Rw)
      (weakCap x.inst) ≤ weakWeight x.inst x.i := (hLw x.inst.request).trans hLs
  have hNw : x.inst.physical.Nw ≤ weakCap x.inst := by
    have := Nat.le_mul_of_pos_left x.inst.physical.Nw x.inst.physical.Jw_pos
    unfold weakCap; omega
  have hXok := oldCtx_ok hcert (weakKappa x.inst x.i) hLC.hΔ.le hres.2
    (fun L hL => hLC.hKg L (hL.trans hLo)) (fun k L hL => hLC.hKd k L (hL.trans hLo))
    (Δ := inhDelta x.inst.physical) (S := (inhData plan x.inst.request).S)
  have hρpos := hεpos ((x.stage x.i).level - 1)
  have hSl : ENNReal.ofReal |x.inst.D.eps ((x.stage x.i).level - 1)| *
      ((weakKappa x.inst x.i).Cslow / ENNReal.ofReal (x.inst.D.eps ((x.stage x.i).level - 1) *
        inhDelta x.inst.physical)) ≤ (inhData plan x.inst.request).S :=
    (slow_le hρpos.le le_rfl hρpos).trans hLC.hS
  have hη : x.inst.D.kap (x.stage x.i).level / x.inst.D.kap ((x.stage x.i).level - 1) = 1 := by
    rw [hkapi, hkapi', div_self hκM.ne']
  -- the finer outputs
  have hfine := fun (k : ℤ) (hk : Odd k) (d₁ : ℕ) (_ : 1 ≤ d₁) (_ : d₁ ≤ n)
      (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2) =>
    inheritedFine hΛ1 hζ hκb hb hεn (x.stage x.i) hN hND hcert hGen hT wd π n
      (w.Cc (.inherited wd h π n)) (Cc' (.inherited wd h π n)) w.Cc0
      (fun k A hA => hL' (.inherited wd h π n) k A hA)
      (fun k A hA τ hτ X hX hh hle n' m α z v u =>
        hAg (.inherited wd h π n) trivial k A hA τ hτ X hX hh hle n' m α z v u)
      hNw (by omega) (by omega) hnN (by omega) (weakKappa x.inst x.i) hXok (fun _ => le_rfl) hSl
      (by rw [hη]; exact zero_le_one) (by rw [hη])
      ((GenSem.UEnv.liftWt_mono _ hhH hNw).trans hlw)
      ((GenSem.UEnv.liftWt_mono _ hhH hnN).trans hlw)
      k hk d₁ I₁ i₀
  -- the coefficient of the identity
  have hfl := w.flux v' u' γ'
  rw [hs] at hfl
  obtain ⟨e, Δ', leaf, hE, hΔ', hLCert, hSF, hsum⟩ := pathMean_ledger_entry hζ hΛ1 hb hstart
    ((x.stage x.i).recap (weakCap x.inst) hN noExports)
    ((x.stage (x.i - 1)).recap (weakCap x.inst) hN' noExports) hcert
    (fun _ he => False.elim he) (fun _ he => False.elim he)
    (show (x.stage x.i).level = (x.stage (x.i - 1)).level + 1 by omega)
    (x.inst.D.eps ((x.stage x.i).level - 1)) n n 1
    ((WeakSource.inherited wd h π n).fluxOp (x.inst.D.eps ((x.stage x.i).level - 1))
      (w.Cc (.inherited wd h π n)) w.Cc0) γ'
    (fun p ctx d I t Y z hd => hfl p ctx d I t Y z hd) hnN (weakKappa x.inst x.i)
    (weakReserve x.inst (x.i - 1)) (weakWeight x.inst (x.i - 1)) hfine
    (fun d₁ _ _ => by
      have h1 : ((n - 1 - (d₁ - 1) : ℕ) : ℝ) * inhDelta x.inst.physical ≤
          (weakCap x.inst : ℝ) * inhDelta x.inst.physical :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast (by omega : n - 1 - (d₁ - 1) ≤ weakCap x.inst)) (inhDelta_pos _).le
      linarith)
    (hεpos _) (Applications.eps_le_one hq hΛ) (Construction.Stream.ocTau_pos hΛ1) hLC.ha3 hLC.hΔ
    (by linarith) hLC.hK0 hLC.hW0 hLC.hC0 hLC.hWr0 hLC.hK hLC.hW hLC.hCold
    ((wsum_mono_weight le_rfl hLn _).trans hLC.hWr) d I kk
  refine ⟨e, Δ', leaf, fun p => ⟨(hE p).1, (hE p).2.1⟩,
    ⟨fun p => Classical.choose (hE p).2.2, fun p => (Classical.choose_spec (hE p).2.2).1,
      fun p ctx t ht X z => (Classical.choose_spec (hE p).2.2).2 ctx t ht X z⟩,
    hΔ', hLCert, hSF, fun p => driftIn_ctx leaf (e p)
      (by show x.i ≤ (x.stage (x.i - 1)).level + 1; rw [hlev']; omega),
    hsum.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  -- the bound
  rw [hrec.1, hrec.2.1, hrec.2.2]
  have hKdef : Kinh plan x.inst.request C =
      4 ^ weakCap x.inst * (((weakCap x.inst : ℕ) : ℝ) + 1) *
        tConst (inhData plan x.inst.request).K (inhData plan x.inst.request).Cold
          (inhDelta x.inst.physical) ^ weakCap x.inst *
        ((inhData plan x.inst.request).Wr * (inhData plan x.inst.request).K *
          (inhData plan x.inst.request).W *
          (fluxMax (inhKappa x.inst.base x.inst.physical) (inhData plan x.inst.request).S
            (inhData plan x.inst.request).Kg (inhData plan x.inst.request).Kd (weakCap x.inst)
            (x.inst.physical.Jw * x.inst.physical.Rw) (weakCap x.inst) : ℝ)) *
        (((weakCap x.inst : ℕ) : ℝ) ^ (x.inst.physical.Jw * x.inst.physical.Rw) *
          max 1 (2 ^ weakCap x.inst * C) ^ (x.inst.physical.Jw * x.inst.physical.Rw)) := rfl
  have hρE : x.inst.D.eps (x.stage (x.i - 1)).level =
      x.inst.D.eps ((x.stage x.i).level - 1) := by rw [hlev', hlevi]
  have hDst : ocDStar x.inst.D.q x.inst.D.Λ (x.stage x.i).level
      (x.inst.D.kap (x.stage x.i).level) (x.inst.D.kap ((x.stage x.i).level - 1)) =
      x.inst.D.eps (x.stage x.i).level := by
    unfold ocDStar
    rw [hkapi, hkapi', div_self hκM.ne', Real.sqrt_one, mul_one]
    rfl
  have hD : ocDStar x.inst.D.q x.inst.D.Λ (x.stage x.i).level
      (x.inst.D.kap (x.stage x.i).level) (x.inst.D.kap ((x.stage x.i).level - 1)) ^ 2 =
      x.inst.D.kap (x.stage (x.i - 1)).level * x.inst.D.cellScaleSq (x.stage x.i).level := by
    rw [hDst, hkap']
    unfold OCData.cellScaleSq
    rw [hkapi]
    field_simp
  rw [hKdef]
  exact inh_coeff_bound x.inst.D hcert π
    (UEnv.fluxXc (oldCtx hcert (weakKappa x.inst x.i) (inhDelta x.inst.physical)
      (weakReserve x.inst x.i) (inhData plan x.inst.request).S (inhData plan x.inst.request).Kg
      (inhData plan x.inst.request).Kd) (weakCap x.inst)
      (liftB (oldCtx hcert (weakKappa x.inst x.i) (inhDelta x.inst.physical)
        (weakReserve x.inst x.i) (inhData plan x.inst.request).S (inhData plan x.inst.request).Kg
        (inhData plan x.inst.request).Kd) (weakCap x.inst)) h n)
    hnN hLC.hK0 hLC.hW0
    (one_le_tConst hLC.hK0 hLC.hC0 hLC.hΔ) hLC.hWr0 hρpos
    (by show 0 < x.inst.D.kap (x.stage (x.i - 1)).level; rw [hkap']; exact hκM)
    (EntryWeakProofs.weakData_cellScaleSq_pos x.inst.D hΛ1 hζ hκb (x.stage x.i).level) hDst hD
    hρE hn2 (by positivity) (fun j _ => x.incoming_length_le _ _ _)
    (NNReal.coe_le_coe.mpr (fluxXc_le_fluxMax (X := oldCtx hcert (weakKappa x.inst x.i)
      (inhDelta x.inst.physical) (weakReserve x.inst x.i) (inhData plan x.inst.request).S
      (inhData plan x.inst.request).Kg (inhData plan x.inst.request).Kd)
      (κ := inhKappa x.inst.base x.inst.physical) (SameConsts.mk rfl rfl rfl) _ hhH hnN)) hhH
    (by unfold weakCap; omega) (hεn _) (Kinh_nonneg plan x.inst.request C)

/-- **The inherited ledger: the entries of the inherited sources**, with the constant map `Kinh`. -/
theorem weakInheritedLedger (hplan : WeakComplexContextPlanOK plan) (hLw : WeakInhPlanOK plan)
    (hHR : WeakHighReserveLiftsStatement plan) : WeakInheritedLedgerStatement plan (Kinh plan) := by
  intro x C hC hW
  refine ⟨Kinh_nonneg plan x.inst.request C, fun w v' u' γ' hinh => ?_⟩
  generalize hs : (w.e v' u' γ').1 = s at hinh
  cases s with
  | inherited wd h π n => exact weakInherited_entry hplan hLw hHR x hC hW w v' u' γ' hs
  | eddy => exact False.elim hinh

end AVRegularity.Providers.WeakGen
end
end

section
/-! **The eddy finer outputs as slot family functions** (weak entry, eddy ledger). From the lift
sequences of the grade-zero family over the slot `k` of the level `m` (no edge), generation gives the
cut-off lift setup (`exists_liftGenSetup`), and the eddy mean of `eddyFamRepP` becomes a graded slot
family function in the eddy context, equal on the admissible families and the window to the
coefficient of the eddy flux (`eddySlotFam`): the eddy flux reads its lifts at the offset `0` only
(`weakEddyFlux_congr0`), where the cut-off lifts agree with the given ones. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal

namespace AVRegularity.Providers.WeakGen

open GenSem CascadeInvariants Majorant

variable {D : OCData} {b : ℝ} {j₀ : ℕ} {Dm : ℕ}
  {κ₁ : MajConsts} {Δ a₀ μ₀ : ℝ} {L₀ : ℕ} {S Kg Kd : ℝ≥0}

/-- **The coefficients of the eddy flux are graded slot family functions, with the drift
twice.** -/
theorem eddySlotFam (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκb : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (m : ℕ) (k : ℤ) (hk : Odd k)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) {R Nl : ℕ}
    (hNR : Nl + Dm + 2 ≤ R)
    (hlift : ∀ A, IsAdmissibleChain D b j₀ m k A →
      IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A (D.eps (m - 1))
          (fun _ _ _ => []))
        R R (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) Nl 0 (Cc A))
    (hX₁ : (topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd).Ok)
    (hSl : ENNReal.ofReal |D.eps (m - 1)| * (κ₁.Cslow / ENNReal.ofReal (D.eps (m - 1) * Δ)) ≤ S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1)
    (hL₀ : UEnv.liftWt Dm 0 Nl ≤ L₀) {n : ℕ} (hn : 2 ≤ n) (hLn : n - 1 ≤ L₀) (ha₀ : 0 ≤ a₀)
    {κ : MajConsts} {Dd lam : ℝ≥0} (hl0 : (lam : ℝ≥0∞) ≠ 0) (hl1 : (lam : ℝ≥0∞) ≤ 1)
    (hd : ∀ c h, κ.drift c h ≤ lam * κ₁.drift c h)
    (hg : ∀ L h, κ.geo .own L h ≤ κ₁.geo .own L h) (hg0 : ∀ L h, h ≠ 0 → κ.geo .own L h = 0)
    (hCold : κ.Cold ≤ κ₁.Cold) (hCslow : κ.Cslow ≤ κ₁.Cslow)
    (hDd : ∀ c h, κ.drift c h ≤ if h = 0 then 0 else (Dd : ℝ≥0∞))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (κc : Fin 2) :
    SlotFamRepP D b j₀ (fun {_ _} _ => False) m k (eddyCtx D (topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd) κ m)
      (fun t A => fluxCoeff (weakEddyFlux D m (D.eps (m - 1))
        (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A (D.eps (m - 1))
          (fun _ _ _ => [])) (Cc A) n t) d I 0 κc)
      (n - 1 - (d - 1))
      (Real.toNNReal |LiftGenSetup.pathMeanPref D m (D.eps (m - 1)) n d| *
        (((Finset.univ : Finset (Equiv.Perm (Fin (d - 1)))).card : ℝ≥0) *
          (Dd * lam * liftB (topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd) Dm 0 (n - 1)))) := by
  set ρ := D.eps (m - 1) with hρ
  have hε : ρ ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκb m
  have hset : CutoffLiftSetup (h := 0) (Dm := Dm) D b j₀ (fun {_ _} _ => False) m k ρ
      (fun _ _ _ _ => []) Cc R R Nl R :=
    exists_liftGenSetup D hΛ hζ hκb b j₀ _ m k hk ρ (div_ne_zero hε hε) _ Cc le_rfl le_rfl hNR
      (fun A hA => WeakEntryProofs.liftSequenceOn_of_global _ _ _ _ _ _ _ _ _ (hlift A hA))
      (fun A hA τ hτ v u d γ hγ α c => by simp [familyLiftData, liftEdges] at hγ)
      (fun U hU v u d α kk =>
        ⟨_, (UEnv.urep_const _ 0).congr fun l _ X _ z => by simp [familyLiftData, liftEdges]⟩)
  obtain ⟨edge', Cc', U, hS, hU⟩ := hset
  have hed : ∀ (v u : Fin 1) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (c : Fin 2),
      (liftEnv D b j₀ (fun {_ _} _ => False) m k ρ {A | IsAdmissibleChain D b j₀ m k A} U
        (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)).IsURepP
        (topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd) (fun l Y z =>
          (((familyLiftData D m k l.1 ρ (edge' l.1)).edge v u d).map
            fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 0 := fun v u d α c =>
    (UEnv.isURepP_zero hX₁ _ 0 0).congr fun l hl Y hY z => by
      have h := Uniqueness.list_sum_map_forall₂
        (f := fun γ : Constituent d.1 ℝ ℝ => γ.map 1 * γ.coeff α l.2 Y z c)
        (g := fun γ : Constituent d.1 ℝ ℝ => γ.map 1 * γ.coeff α l.2 Y z c)
        ((hU l.1 hl.1).2.2.2.1.edge v u d) fun γ γ' hγ => by rw [hγ.1, hγ.2 α l.2 Y hY z]
      rw [← h]
      simp [familyLiftData, liftEdges]
  have hfam := eddyFamRepP hS hX₁ hSl hη0 hη1 hed hL₀ (fun A hA => (hU A hA).2.1) hn hLn ha₀ hl0
    hl1 hd hg hg0 hCold hCslow hDd d I κc
  refine (SlotFamRepP.of_famURepP hc hfam).congr fun A hA t ht => ?_
  obtain ⟨-, h0, -, hag, hCeq, hreg⟩ := hU A hA
  have hτ := inv_mul_mem_liftWindowOf hc ht
  have hregA := hreg 0 le_rfl n (Dm + 2) (by omega) _ hτ 0
  have hfl := fluxCoeff_weakEddyFlux D m (ρ := ρ) (familyLiftData D m k A ρ (edge' A)) (Cc' A) n t
    (by omega) hregA d I κc
  have hcongr : fluxCoeff (weakEddyFlux D m ρ (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ)
      D m k A ρ (fun _ _ _ => [])) (Cc A) n t) d I 0 κc =
      fluxCoeff (weakEddyFlux D m ρ (familyLiftData D m k A ρ (edge' A)) (Cc' A) n t) d I 0 κc := by
    unfold fluxCoeff
    rw [weakEddyFlux_congr0 D m ρ hag.eta hag.drift n t
      (fun m' α z => (congrFun (hCeq 0 (n - 1) m' α _ 0 h0) z).symm)]
  rw [hcongr, hfl]
  simp only [LiftGenSetup.pathMeanPref, fluxXA, mulArr, familyLiftData]

open scoped Classical in
/-- **The ledger entries of a transferred finer output of path-mean size, over a general fine
context** (`pathMean_ledger_entry` of the ledger with the fine context `X` in place of the old
certificate's context; the leaves are those of `X`). -/
theorem transferEntryGen {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G' : GenStage D hr Dm b j₀) {𝒮o : SeedExports}
    (hexp : ∀ {i p} (e : Gen .ctx i p), 𝒮o e → G'.exports e) {m : ℕ} (hlev : m = G'.level + 1)
    (ρ : ℝ) (n Dγ : ℕ) (lam : ℝ) (fop : FamFluxOp) {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u')
    (hflux : ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G'.level p) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (Y z : Vec 2), 2 ≤ d →
      G'.fam.flux p ctx v' u' γ' d I t Y z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (ctx.1.recenter D (D.eps (G'.level - 1) • Y))
        then transferAt D m p.1 lam Dγ fop t
          (ctx.1.recenter D (D.eps (G'.level - 1) • Y)) z d I
        else 0)
    (hDγ : Dγ ≤ Dm) {X : GCtx} (hXT : ∀ t, t ∈ X.T)
    (hXlev : ∀ (s : GenSort) (p : ℤ) (e : Gen s G'.level p), X.leaf e = none)
    (ha₀ : X.a₀ = 3 * Real.pi * b) {a K W Cold Wr : ℝ} {FP : ℝ≥0} {r : ℕ → ℕ} (μn : ℝ) (Ln : ℕ)
    (hfine : ∀ k : ℤ, Odd k → ∀ d₁ : ℕ, 1 ≤ d₁ → d₁ ≤ Dγ →
      ∀ (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
        SlotFamRepP D b j₀ 𝒮o m k X (fun t A => fluxCoeff (fop k t A) d₁ I₁ 0 i₀) (r d₁)
          (Real.toNNReal |LiftGenSetup.pathMeanPref D m ρ n d₁| *
            (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) * FP)))
    (hr : ∀ d₁ : ℕ, 2 ≤ d₁ → d₁ ≤ Dγ → μn + (r d₁ : ℝ) * X.Δ ≤ X.μ₀)
    (hε0 : 0 < D.eps G'.level) (hε1 : D.eps G'.level ≤ 1)
    (hτ : 0 < ocTau D.α D.q D.Λ (G'.level + 1))
    (ha3 : 3 * Real.pi * b < a) (hΔ : 0 < X.Δ) (hresΔ : μn + Dm * X.Δ ≤ 2)
    (hK0 : 0 ≤ K) (hW0 : 0 ≤ W) (hC0 : 0 ≤ Cold) (hWr0 : 0 ≤ Wr)
    (hK : ∀ L, L ≤ Dm → kBound X.κ a L ≤ ENNReal.ofReal K)
    (hW : wsum a 0 X.κ.child ≤ ENNReal.ofReal W) (hCold : X.κ.Cold ≤ ENNReal.ofReal Cold)
    (hWr : wsum (3 * Real.pi * b) Ln (expProfile 1 a) ≤ ENNReal.ofReal Wr) :
    ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
      ∃ e : (p : OddSlot) → Gen .ctx G'.level p.1,
        G'.IsExprFor v' u' γ' d α c e ∧ (∀ p, Gen.SolvedFree X.leaf (e p)) ∧
        ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ Ln) *
          ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1,
            genMode D X.κ X.Δ X.leaf (e p) μn h t
          ≤ ENNReal.ofReal (Wr * if 2 ≤ d then
              pmBound D G'.level m ρ n Dγ K W (tConst K Cold X.Δ) lam FP d else 0) := by
  have ha0 : 0 ≤ a := by have := mul_pos Real.pi_pos hb; linarith
  have hfine' : ∀ (d : ℕ) (k : ℤ), Odd k → ∀ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ,
      ∀ (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
        SlotFamRepP D b j₀ 𝒮o (G'.level + 1) k X
          (fun t A => fluxCoeff (fop k t A) d₁ I₁ 0 i₀) (r d₁)
          (Real.toNNReal |LiftGenSetup.pathMeanPref D m ρ n d₁| *
            (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) * FP)) := by
    intro d k hk d₁ hd₁ I₁ i₀
    have h1 := Finset.mem_Icc.mp hd₁
    rw [← hlev]
    exact hfine k hk d₁ (by omega) h1.2 I₁ i₀
  intro d α c
  obtain ⟨e, hE, hSF, hnorm⟩ := exists_transferExpr_of_finer hζ hΛ hb hstart G' (𝒮 := 𝒮o) hexp γ'
    d α c lam Dγ fop (fun hd p ctx t Y z => by rw [hflux p ctx d α t Y z hd, hlev])
    (X := X) hXT hXlev hτ (hfine' d) (mres := μn)
    (fun hd d₁ hd₁ => by
      have h1 := Finset.mem_Icc.mp hd₁
      exact hr d₁ (by omega) h1.2)
  refine ⟨e, hE, hSF, ?_⟩
  refine (ledgerSum_le D X.κ X.Δ X.a₀ X.leaf (by rw [ha₀]; positivity) e ha0 (3 * Real.pi * b) Ln
    μn (ENNReal.ofReal (if 2 ≤ d then
      pmBound D G'.level m ρ n Dγ K W (tConst K Cold X.Δ) lam FP d else 0))
    fun p t _ => ?_).trans ?_
  · refine (hnorm p a 0 t).trans ?_
    split_ifs with hd
    · subst hlev
      exact pm_genNorm_le D X.κ hε0 hε1 hΔ (G'.level + 1) ρ n Dγ Dm hDγ lam FP hK0 hW0 hC0 hK hW
        hCold hresΔ d
    · exact zero_le
  · rw [ENNReal.ofReal_mul hWr0]
    exact mul_le_mul_left hWr _

end AVRegularity.Providers.WeakGen
end
end
end
