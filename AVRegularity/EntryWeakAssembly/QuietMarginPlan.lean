-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.QuietParentPhysicalPrice
public import AVRegularity.EntryWeakAssembly.PairedForcingCostSchur
import AVRegularity.Applications.Transfer.TubeK
import AVRegularity.Proofs.Results.Finite.TraceClosure
import AVRegularity.CycleJoint.ActivePieceDimensionalSmooth
import AVenhance.Infra.Construction.StreamAdmissible

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Close the native parent-jet ingredient with finite physical-order sums.
Every price and threshold precedes the ambient cap and the construction. -/

open AVRegularity.Providers.QuietAtlas AVRegularity.CycleJointProofs

/-- The physical price is chosen only from the physical menu and jet order. -/
def weakQuietPhysicalCost {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (plan : WeakPassagePlan) (R : WeakPassageRequest A) : ℝ :=
  (weak_quiet_native_physical_price A (plan.jetOrder R)).choose

def weakQuietPhysicalFloor {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (plan : WeakPassagePlan) (R : WeakPassageRequest A) : ℕ :=
  (weak_quiet_native_physical_price A (plan.jetOrder R)).choose_spec.2.choose

/-- A single price also absorbs the analytic threshold through the refinement's
ceiling floor. Its finite-order factor uses the weak cap, never Dm. -/
def weakQuietNativePrice (plan : WeakPassagePlan) : WeakQuietPrice := fun {_B} {A} R =>
  max (((1 + A.Jw * A.Nw + 1 : ℕ) : ℝ) * weakQuietPhysicalCost plan R *
    weakQuietCertificatePrice R) (weakQuietPhysicalFloor plan R : ℝ)

/-- Orders above the fixed weak cap vanish literally. -/
theorem weak_quiet_physical_above_cap {plan : WeakPassagePlan} {B}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M ≤ i) (hit : i ≤ c.M + A.Jw)
    (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u)
    (d : ℕ) (hd : 1 + A.Jw * A.Nw < d) :
    (c.stage i).physCoeff v u γ d = fun _ _ => 0 := by
  have ho := EntryWeakProofs.weakConstruction_stage_maxOrderBound _ _ _ _ _ _ c.construction
    i hi hit v u γ
  funext t Y
  exact constituentPhysical_zero_above_max (c.stage i).fam _ _ _ (c.stage i).actual
    v u γ d (ho.trans_lt hd) t Y

/-- The native analytic ingredient, with all scalar choices made before Dm. -/
theorem weak_quiet_native_jets (plan : WeakPassagePlan) :
    WeakQuietNativeJetsStatement (weakQuietParentJetPlan plan (weakQuietNativePrice plan))
      (fun R => max 0 (weakQuietNativePrice plan R)) := by
  let price : WeakQuietPrice := weakQuietNativePrice plan
  intro hcommon B A R c r i hi hit _hw hquiet
  let cap := 1 + A.Jw * A.Nw
  let C := weakQuietPhysicalCost plan R
  let Mf := weakQuietPhysicalFloor plan R
  have hC : 0 ≤ C := (weak_quiet_native_physical_price A (plan.jetOrder R)).choose_spec.1
  have hcert : 0 ≤ weakQuietCertificatePrice R :=
    Finset.sum_nonneg (fun _ _ => le_max_left 0 _)
  have hM : Mf ≤ c.M := by
    have hfloor : ⌈max 0 (price R)⌉₊ ≤ c.M :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans c.level_ge
    have hm : (Mf : ℝ) ≤ max 0 (price R) :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hh := hm.trans (Nat.le_ceil (max 0 (price R)))
    have hh' : Mf ≤ ⌈max 0 (price R)⌉₊ := by exact_mod_cast hh
    exact hh'.trans hfloor
  have hphysical := (weak_quiet_native_physical_price A (plan.jetOrder R)).choose_spec.2.choose_spec
    (weakQuietParentJetPlan plan price) hcommon R c r i hM hi hit hquiet
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans
      (((weakQuietParentJetPlan plan price).base_ge B).trans c.base_ge)
  have hE : 0 < c.D.eps (i - 1) := Construction.Stream.ocEpsilon_pos hΛ
  have hζ : IsFastProfile c.D.ζ := by rw [c.profile_eq]; exact B.hζ
  have hband : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [c.alpha, c.q_eq, c.base_eq, c.profile_eq, c.terminal]
    exact c.band
  have hν : 0 < c.D.κ c.M := CycleReference.bandChain_pos hΛ hζ hband (by rw [c.terminal])
  have hz (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u)
      (d : ℕ) (hd : cap < d) : (c.stage i).physCoeff v u γ d = fun _ _ => 0 :=
    weak_quiet_physical_above_cap c i hi.le hit v u γ d hd
  refine ⟨?_, ?_⟩
  · intro v u γ d hd _hdm t ht
    by_cases hdc : d ≤ cap
    · exact (hphysical v u γ d hd hdc).1 t ht
    · rw [hz v u γ d (by omega)]
      exact contDiff_const
  · intro v u
    let F := fun (γ : (c.stage i).fam.Γ v u) (d : ℕ) =>
      coefficientSeminorm (c.D.eps (i - 1)) (plan.jetOrder R)
        (r.tq i - ocTauP c.D.α c.D.q c.D.Λ i / 2) (r.tq i)
        ((c.stage i).physCoeff v u γ d) *
        (ENNReal.ofReal (c.D.κ c.M * c.D.eps (i - 1) ^ (d - 2)))⁻¹
    have hF (γ : (c.stage i).fam.Γ v u) (d : ℕ) (hd : 2 ≤ d) (hdc : d ≤ cap) :
        F γ d ≤ ENNReal.ofReal (C * (weakQuietCertificatePrice R *
          ((c.stage i).fam.identity v u γ).record.size)) := by
      have hh := (hphysical v u γ d hd hdc).2
      change _ ≤ ENNReal.ofReal (C * (weakQuietCertificatePrice R *
        ((c.stage i).fam.identity v u γ).record.size) *
          (c.D.κ c.M * c.D.eps (i - 1) ^ (d - 2))) at hh
      have ha : 0 ≤ C * (weakQuietCertificatePrice R *
          ((c.stage i).fam.identity v u γ).record.size) :=
        mul_nonneg hC (mul_nonneg hcert ((c.stage i).fam.identity v u γ).record.size_nonneg)
      have hden : 0 < c.D.κ c.M * c.D.eps (i - 1) ^ (d - 2) := mul_pos hν (pow_pos hE _)
      apply (mul_le_mul_of_nonneg_right hh zero_le).trans_eq
      rw [ENNReal.ofReal_mul ha, mul_assoc,
        ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hden)) ENNReal.ofReal_ne_top,
        mul_one]
    have hsum (γ : (c.stage i).fam.Γ v u) :
        (∑ d ∈ Finset.Icc 2 c.Dm, F γ d) ≤
          ENNReal.ofReal (((cap + 1 : ℕ) : ℝ) * C * weakQuietCertificatePrice R *
            ((c.stage i).fam.identity v u γ).record.size) := by
      have hs : (∑ d ∈ Finset.Icc 2 c.Dm, F γ d) = ∑ d ∈ Finset.Icc 2 cap, F γ d := by
        symm
        apply Finset.sum_subset
        · intro d hd
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
            (Finset.mem_Icc.mp hd).2.trans c.order_ge⟩
        · intro d hd hnot
          have hd' : cap < d := by have := Finset.mem_Icc.mp hd; simp only [Finset.mem_Icc] at hnot; omega
          dsimp only [F]
          rw [hz v u γ d hd', coefficientSeminorm_zero_function, zero_mul]
      rw [hs]
      have ha : 0 ≤ C * (weakQuietCertificatePrice R *
          ((c.stage i).fam.identity v u γ).record.size) :=
        mul_nonneg hC (mul_nonneg hcert ((c.stage i).fam.identity v u γ).record.size_nonneg)
      calc
        _ ≤ ∑ d ∈ Finset.Icc 2 cap, ENNReal.ofReal (C * (weakQuietCertificatePrice R *
            ((c.stage i).fam.identity v u γ).record.size)) :=
          Finset.sum_le_sum (fun d hd => hF γ d (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2)
        _ = ENNReal.ofReal (∑ _d ∈ Finset.Icc 2 cap, C * (weakQuietCertificatePrice R *
            ((c.stage i).fam.identity v u γ).record.size)) :=
          (ENNReal.ofReal_sum_of_nonneg (fun _ _ => ha)).symm
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hc : (Finset.Icc 2 cap).card ≤ cap + 1 := by
            have hh : Finset.Icc 2 cap ⊆ Finset.range (cap + 1) := by
              intro d hd
              exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hd).2; omega)
            simpa only [Finset.card_range] using Finset.card_le_card hh
          have hh := mul_le_mul_of_nonneg_right (show ((Finset.Icc 2 cap).card : ℝ) ≤ cap + 1 by
            exact_mod_cast hc) ha
          simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using hh
    have hsumγ : (∑ γ : (c.stage i).fam.Γ v u, ∑ d ∈ Finset.Icc 2 c.Dm, F γ d) ≤
        ENNReal.ofReal (((cap + 1 : ℕ) : ℝ) * C * weakQuietCertificatePrice R *
          ∑ γ : (c.stage i).fam.Γ v u, ((c.stage i).fam.identity v u γ).record.size) := by
      apply (Finset.sum_le_sum (fun γ _ => hsum γ)).trans_eq
      rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => by
        have hs := ((c.stage i).fam.identity v u γ).record.size_nonneg
        positivity), ← Finset.mul_sum]
    have hp : ((cap + 1 : ℕ) : ℝ) * C * weakQuietCertificatePrice R ≤ max 0 (price R) :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hmass : 0 ≤ Real.sqrt (weakMass c.D A.Nw A.Jw A.η₀ u.1 /
        weakMass c.D A.Nw A.Jw A.η₀ v.1) := Real.sqrt_nonneg _
    apply (mul_le_mul_of_nonneg_left hsumγ zero_le).trans
    rw [← ENNReal.ofReal_mul hmass]
    apply ENNReal.ofReal_le_ofReal
    have hsizes : 0 ≤ ∑ γ : (c.stage i).fam.Γ v u, ((c.stage i).fam.identity v u γ).record.size :=
      Finset.sum_nonneg (fun γ _ => ((c.stage i).fam.identity v u γ).record.size_nonneg)
    have hh := mul_le_mul_of_nonneg_right hp (mul_nonneg hmass hsizes)
    simpa only [weakStoredEdgeWeight, ← Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hh

/-- The exact parent jets of the coefficient layer, with the native analytic price discharged. -/
theorem weak_middle_half_jets (plan : WeakPassagePlan) :
    WeakMiddleHalfJetsStatement (weakQuietParentJetPlan plan (weakQuietNativePrice plan)) :=
  weak_middle_half_jets_of_native_budget plan (weakQuietNativePrice plan)
    (weak_quiet_native_jets plan)

/-- Include the heat-window geometry floor before choosing the native price.
This changes only the level floor. -/
def weakQuietGeometryRefinement (plan : WeakPassagePlan) : WeakPassagePlan :=
  { plan with
    levelFloor := fun {B} {A} R j =>
      max (plan.levelFloor R j) (weakQuietGeometryFloor B A.Λ) }

/-- The complete coefficient refinement preserves radius and derivative reserves. -/
def weakQuietCoefficientPlan (plan : WeakPassagePlan) : WeakPassagePlan :=
  weakQuietParentJetPlan (weakQuietGeometryRefinement plan)
    (weakQuietNativePrice (weakQuietGeometryRefinement plan))

/-- The coefficient layer: actual parent coefficient jets and the heat-window fit on the trimmed
backward middle half, with every native analytic ingredient discharged. -/
theorem weak_quiet_coefficient (plan : WeakPassagePlan) :
    WeakQuietCoefficientStatement (weakQuietCoefficientPlan plan) := by
  let p := weakQuietGeometryRefinement plan
  have hgeometry : WeakQuietGeometryPlanOK (weakQuietCoefficientPlan plan) :=
    weak_quiet_geometry_plan_of_threshold _ (fun R j =>
      (le_max_right _ _).trans (le_max_left _ _))
  intro B A R c r i hi hit hw
  exact weak_quiet_coefficient_of_parent_jets (weakQuietCoefficientPlan plan) hgeometry
    (weak_quiet_parent_jet_plan_spec p (weakQuietNativePrice p)).1
    (weak_middle_half_jets p) c r i hi hit hw

end AVRegularity.WeakEntryProofs.Assembly
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
namespace AVRegularity.WeakEntryProofs.ReadoutLinear

/-! **Linearity of the weak readout on `C^{L_w+3}` fields**.

`weakReadoutLinear : WeakReadoutLinearStatement plan`, under the single plan condition
`WeakReadoutLinearPlanOK plan`: the lift-order floor of the plan is at least the readout order,
`L_w ≤ plan.liftFloor A` (no condition on `levelFloor`, `baseFloor`).

Proof. Downward induction over the levels (`readoutLinear_chain`). A field on the components of the
stage `i` of class `C^{d N_w}`, where `i + d = M + J_w`, has `W i` additive and homogeneous:
* `d = 0`: `W (M + J_w)` is the value at the root component (`IsWeakReadoutChain`, the root is the
  one component of the top stage);
* `d + 1`: `W i = W (i + 1) ∘ Λ_{i+1} ∘ 𝓡_{i+1}`; the readout step keeps the class `C^{(d+1) N_w}`,
  the glued lift is additive and homogeneous on the `C^{N_w}` input, and the lifted field is
  `C^{d N_w}` because the lift coefficients are box smooth of order `sX, sZ ≥ L_w ≥ d N_w`
  (`IsWeakReadoutLifts`, clause 6 of `IsLiftSequence`; only odd slots occur).

Count of derivatives: the stage `M` carries `C^{J_w N_w} = C^{L_w}` (`x.readout_order`), each of the
`J_w` levels uses `N_w` derivatives, so the top stage uses `0`; the order required of the lift
coefficients is `≤ (J_w - 1) N_w ≤ L_w`.

Special cases: `J_w = 1` (one glued lift, inputs `C^{N_w}`); `z₂ = 0`; `c = 0`; a time with no
observed pulse (the glued lift is `0`). -/

/-- **The plan condition for the linearity of the weak readout**: the lift-order floor of the plan
is at least the readout order `L_w`. -/
def WeakReadoutLinearPlanOK (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B), A.Lw ≤ plan.liftFloor A

section Chain

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C}

/-- The cell time scale of every level is positive. -/
theorem readoutLinear_cell_pos (m : ℕ) : 0 < x.D.cellScaleSq m := by
  have hΛ1 : 1 ≤ x.D.Λ := by
    rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans x.base128
  have hζ : IsFastProfile x.D.ζ := by rw [x.profile_eq]; exact B.hζ
  have hband : IsOCBandChain x.D.α x.D.q x.D.Λ x.D.ζ x.D.term x.D.κ := by
    rw [x.alpha, x.q_eq, x.base_eq, x.profile_eq, x.terminal]; exact x.band
  exact EntryWeakProofs.weakData_cellScaleSq_pos x.D hΛ1 hζ hband m

/-- The pulse time scale of every level is positive. -/
theorem readoutLinear_tau_pos (m : ℕ) : 0 < ocTau x.D.α x.D.q x.D.Λ m := by
  have hΛ1 : 1 ≤ x.D.Λ := by
    rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans x.base128
  exact Construction.Stream.ocTau_pos hΛ1

variable {g : WeakEntryStages x} (s : WeakEntrySchedule g)

/-- The root component lies in the top stage. -/
theorem readoutLinear_root_mem :
    (⟨0, []⟩ : Comp) ∈ (g.stage (x.M + A.Jw)).comps := by
  rw [g.construction.2.1.2.1]
  exact Finset.mem_singleton_self _

include s in
/-- **Linearity of `W i` on `C^{d N_w}` fields**, `i + d = M + J_w`. -/
theorem readoutLinear_chain (hok : WeakReadoutLinearPlanOK plan) :
    ∀ d : ℕ, ∀ i : ℕ, i + d = x.M + A.Jw → d ≤ A.Jw → ∀ (t : ℝ)
      (g₁ g₂ : CompIn (g.stage i).comps → Vec 2 → ℝ) (c : ℝ),
      (∀ v, ContDiff ℝ ((d * A.Nw : ℕ) : ℕ∞) (g₁ v)) →
      (∀ v, ContDiff ℝ ((d * A.Nw : ℕ) : ℕ∞) (g₂ v)) →
      s.W i t (fun v y => g₁ v y + c • g₂ v y) = s.W i t g₁ + c • s.W i t g₂ := by
  intro d
  induction d with
  | zero =>
    intro i hi _ t g₁ g₂ c _ _
    obtain rfl : i = x.M + A.Jw := by omega
    funext y
    have hr := readoutLinear_root_mem (g := g)
    rw [s.chain.1 t (fun v y => g₁ v y + c • g₂ v y) y hr, Pi.add_apply, Pi.smul_apply,
      s.chain.1 t g₁ y hr, s.chain.1 t g₂ y hr]
  | succ d ih =>
    intro i hi hd t g₁ g₂ c h₁ h₂
    have hstep : ∀ g' : CompIn (g.stage i).comps → Vec 2 → ℝ, s.W i t g' =
        s.W (i + 1) t (weakGluedLift (i + 1) A.Nw (A.Jw * A.Rw) (g.stage (i + 1))
          (s.CcR (i + 1)) t (weakReadoutStep (i + 1) A.η₀ (g.stage (i + 1)) (g.stage i) g')) :=
      fun g' => s.chain.2 (i + 1) (by omega) (by omega) t g'
    have hN : ((d + 1) * A.Nw : ℕ) = d * A.Nw + A.Nw := Nat.succ_mul d A.Nw
    have hcN := readoutLinear_cell_pos (x := x) (i + 1)
    have hτ := readoutLinear_tau_pos (x := x) (i + 1)
    have hr : d * A.Nw ≤ A.Lw := by
      rw [x.readout_order]; exact Nat.mul_le_mul_right _ (by omega)
    have hX : d * A.Nw ≤ R.sX := hr.trans ((hok A).trans x.sX_ge)
    have hZ : d * A.Nw ≤ R.sZ := hr.trans ((hok A).trans x.sZ_ge)
    have hs₁ : ∀ v, ContDiff ℝ ((d * A.Nw + A.Nw : ℕ) : ℕ∞)
        (weakReadoutStep (i + 1) A.η₀ (g.stage (i + 1)) (g.stage i) g₁ v) :=
      readoutLinear_step_contDiff _ _ _ _ g₁ (by rw [← hN]; exact h₁)
    have hs₂ : ∀ v, ContDiff ℝ ((d * A.Nw + A.Nw : ℕ) : ℕ∞)
        (weakReadoutStep (i + 1) A.η₀ (g.stage (i + 1)) (g.stage i) g₂ v) :=
      readoutLinear_step_contDiff _ _ _ _ g₂ (by rw [← hN]; exact h₂)
    have hNle : (((A.Nw : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((d * A.Nw + A.Nw : ℕ) : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_add_left _ _
    have hl₁ := readoutLinear_lift_contDiff (g.stage (i + 1)) (i + 1) A.Nw (A.Jw * A.Rw)
      (s.CcR (i + 1)) t (d * A.Nw) hcN hτ (s.lifts (i + 1) (by omega) (by omega)) hX hZ _ hs₁
    have hl₂ := readoutLinear_lift_contDiff (g.stage (i + 1)) (i + 1) A.Nw (A.Jw * A.Rw)
      (s.CcR (i + 1)) t (d * A.Nw) hcN hτ (s.lifts (i + 1) (by omega) (by omega)) hX hZ _ hs₂
    have hadd := readoutLinear_lift_add_smul (g.stage (i + 1)) (i + 1) A.Nw (A.Jw * A.Rw)
      (s.CcR (i + 1)) t hcN.ne' _ _ c (fun v => (hs₁ v).of_le hNle) (fun v => (hs₂ v).of_le hNle)
    rw [hstep, hstep g₁, hstep g₂, readoutLinear_step_add_smul, hadd]
    exact ih (i + 1) (by omega) (by omega) t _ _ c hl₁ hl₂

end Chain

/-- **The weak readout is linear on `C^{L_w+3}` fields** (`WeakReadoutLinearStatement`). -/
theorem weakReadoutLinear (plan : WeakEntryGluePlan) (hok : WeakReadoutLinearPlanOK plan) :
    WeakReadoutLinearStatement plan := by
  intro B A R C x g s t z₁ z₂ c h₁ h₂
  have hle : (((A.Jw * A.Nw : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((A.Lw + 3 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (by rw [← x.readout_order]; omega : A.Jw * A.Nw ≤ A.Lw + 3)
  exact readoutLinear_chain s hok A.Jw x.M (by omega) le_rfl t
    (fun v y => z₁ (g.relabel v) y) (fun v y => z₂ (g.relabel v) y) c
    (fun v => (h₁ _).of_le hle) (fun v => (h₂ _).of_le hle)

end AVRegularity.WeakEntryProofs.ReadoutLinear
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Buffer
namespace AVRegularity.WeakEntryProofs.Assembly

/-! The parent velocity satisfies the scalar drift conditions uniformly in the
ambient order cap. The weak scale ledger fixes the terminal threshold; the
radius cap is absolute and the finite jet order is chosen afterwards. -/

/-- The weak ledger absorbs the parent drift strain at the entire parent
wavelength. This terminal threshold is independent of both jet order and Dm. -/
theorem weak_parent_drift_strain_threshold (B : WeakCoefficientBase)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M ≥ M₀, ∀ ν ∈ ocBand B.α B.q Λ M,
      ∀ i : ℕ, M < i →
      (actualDriftJetConstant * ocA B.α B.q Λ (i - 1)) * 1024 *
        ocEpsilon B.q Λ (i - 1) ^ 2 ≤ ν / 8 := by
  obtain ⟨C, hC, hscale⟩ := EntryScales.weak_scales_core B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
  have hCp : 0 < C := zero_lt_one.trans_le hC
  let W := actualDriftJetConstant * 1024
  have hW : 0 ≤ W := mul_nonneg actualDriftJetConstant_nonneg (by norm_num)
  have hWp : 0 < W + 1 := by linarith only [hW]
  obtain ⟨N, hN⟩ := Providers.exists_parent_rpow_lt B.hq.1 hΛ
    (Scales.admissible_exponent_facts B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq).1
    (show 0 < 1 / (8 * (W + 1) * C) by positivity)
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro M hM ν hν i hi
  have hE : 0 < ocEpsilon B.q Λ M := (Scales.epsilon_basic B.hq.1 hΛ).1
  have hνp : 0 < ν := lt_of_lt_of_le (by
    apply div_pos (Real.rpow_pos_of_pos hE _)
    norm_num) hν.1
  have hs := (hscale Λ hΛ M ν hν i hi).2.1
  have hsmall : C * ocEpsilon B.q Λ (i - 1) ^ ocGamma B.α B.q ≤
      1 / (8 * (W + 1)) := by
    have hh := mul_le_mul_of_nonneg_left (hN i (by omega)).le hCp.le
    convert hh using 1
    field_simp
  have hwsmall : W * (ocA B.α B.q Λ (i - 1) *
      ocEpsilon B.q Λ (i - 1) ^ 2 / ν) ≤ 1 / 8 := by
    calc
      _ ≤ W * (1 / (8 * (W + 1))) :=
        mul_le_mul_of_nonneg_left (hs.trans hsmall) hW
      _ ≤ (W + 1) * (1 / (8 * (W + 1))) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)
      _ = 1 / 8 := by field_simp
  have hh := mul_le_mul_of_nonneg_right hwsmall hνp.le
  calc
    _ = (W * (ocA B.α B.q Λ (i - 1) *
        ocEpsilon B.q Λ (i - 1) ^ 2 / ν)) * ν := by
      dsimp only [W]
      field_simp
    _ ≤ (1 / 8) * ν := hh
    _ = ν / 8 := by ring

/-- One threshold supplies the actual parent scalar environment at every
positive radius ratio at most 1/2048, on every requested time window. -/
theorem weak_parent_scalar_drift_budget (B : WeakCoefficientBase)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M ≥ M₀, ∀ ν ∈ ocBand B.α B.q Λ M,
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq B.α B.q Λ B.ζ Φ →
      ∀ i : ℕ, M < i → ∀ c : ℝ, 0 < c → c ≤ 1 / 2048 →
      ∀ a b : ℝ, ∀ Q : ℕ,
      Nonempty (WeakScalarTorusDrift ν (c * ocEpsilon B.q Λ (i - 1)) a b
        (streamVel (Φ (i - 1))) Q) := by
  obtain ⟨M₀, hM₀, hsmall⟩ := weak_parent_drift_strain_threshold B Λ hΛ
  refine ⟨M₀, hM₀, ?_⟩
  intro M hM ν hν Φ hΦ i hi c hc hcmax a b Q
  have hΛ1 : 1 ≤ Λ := (by norm_num : 1 ≤ 128).trans hΛ
  have he : 0 < ocEpsilon B.q Λ (i - 1) := (Scales.epsilon_basic B.hq.1 hΛ).1
  have hνp : 0 < ν := lt_of_lt_of_le (by
    apply div_pos (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛ1) _)
    norm_num) hν.1
  have ha : 0 ≤ ocA B.α B.q Λ (i - 1) := (Real.rpow_pos_of_pos he _).le
  have hfield := Infra.Construction.smoothPeriodic_streamVel
    (Velocity.streamSeq_admissible B.hζ hΛ hΦ (i - 1))
  have hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (streamVel (Φ (i - 1)) t) := fun t =>
    Applications.streamVel_slice_smooth B.α B.q B.ζ B.hζ Λ hΛ Φ hΦ (i - 1) t
  have hφ : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (Φ (i - 1) t) := fun t =>
    (Velocity.streamSeq_admissible B.hζ hΛ hΦ (i - 1)).1.comp
      (contDiff_const.prodMk contDiff_id)
  refine ⟨{
    nu_pos := hνp
    radius_pos := mul_pos hc he
    measurable := hfield.smooth.continuous.measurable
    bounded := ⟨Applications.velBound B.α B.q Λ, fun t _ x =>
      Applications.streamVel_norm_le B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq
        B.ζ B.hζ Λ hΛ Φ hΦ (i - 1) t x⟩
    smooth := fun t _ => hvs t
    div := ?_
    periodic := fun t _ => Velocity.streamSeq_velocity_spatial_periodic B.hζ hΛ hΦ (i - 1) t
    amplitude := actualDriftJetConstant * ocA B.α B.q Λ (i - 1)
    amplitude_nonneg := mul_nonneg actualDriftJetConstant_nonneg ha
    base := 1024
    base_ge := by norm_num
    length := ocEpsilon B.q Λ (i - 1)
    length_pos := he
    jets := fun j hj _ t _ x => actual_stream_drift_arrays B.α B.s B.hα₀ B.hα₁
      B.hs₀ B.hs₁ B.q B.hq B.ζ B.hζ Λ hΛ Φ hΦ (i - 1) (by omega) t j hj x
    scale := ?_
    strain := ?_ }⟩
  · intro t _ x
    have hh := Applications.streamVel_classical_div hφ t x
    unfold Applications.pd at hh
    rw [Velocity.Port.MaterialSpatial.fderiv_component_apply (hvs t) x 0 0,
      Velocity.Port.MaterialSpatial.fderiv_component_apply (hvs t) x 1 1] at hh
    rw [Fin.sum_univ_two]
    exact hh
  · calc
      1024 * (c * ocEpsilon B.q Λ (i - 1)) / ocEpsilon B.q Λ (i - 1) =
          1024 * c := by field_simp
      _ ≤ 1024 * (1 / 2048) := mul_le_mul_of_nonneg_left hcmax (by norm_num)
      _ = 1 / 2 := by norm_num
  · have hc1 : c ≤ 1 := hcmax.trans (by norm_num)
    have hr : c * ocEpsilon B.q Λ (i - 1) ≤ ocEpsilon B.q Λ (i - 1) :=
      (mul_le_mul_of_nonneg_right hc1 he.le).trans_eq (one_mul _)
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos hc he).le hr 2)
      (mul_nonneg (mul_nonneg actualDriftJetConstant_nonneg ha) (by norm_num))).trans
        (hsmall M hM ν hν i hi)

/-- The scalar strain threshold, fixed before every reserve request. -/
def weakQuietDriftFloor (B : WeakCoefficientBase) (Λ : ℕ) : ℕ :=
  if hΛ : 128 ≤ Λ then (weak_parent_scalar_drift_budget B Λ hΛ).choose else 0

end AVRegularity.WeakEntryProofs.Assembly
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Pre-cap quiet margin reserve and price choices, and the actual middle-half velocity
identity. The latter follows from the pinned slow quiet margin, without any assumption
of independence on untrimmed quiet times. -/

/-- Choose the jet reserve and nonnegative coefficient price before pricing
scalar propagation. Radius selection still belongs to that analytic propagation. -/
def weakQuietReservePlan (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) : WeakPassagePlan :=
  { plan with
    jetOrder := fun {_B} {A} R => max (plan.jetOrder R)
      (R.Kw + max (A.Jw * A.Rw + 1) (prices.depth R) * (1 + A.Jw * A.Nw))
    coeffC := fun R => max 0 (plan.coeffC R)
    levelFloor := fun {B} {A} R j => max (plan.levelFloor R j) (max (weakQuietGeometryFloor B A.Λ) (weakQuietDriftFloor B A.Λ)) }

/-- Scalar prices are chosen after the reserve; the finite polynomial then fixes
traceC. This refinement does not alter the radius, jets or coefficient bound. -/
def weakQuietTracePlan (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) : WeakPassagePlan :=
  { plan with
    traceC := fun R => prices.scalar R 0 + ∑ n ∈ Finset.range (prices.depth R),
      prices.scalar R (n + 1) * plan.coeffC R ^ (n + 1) }

/-- The reserve and trace refinements discharge all purely numerical quiet margin
conditions independently of Dm, the actual family and the scalar datum. -/
theorem weak_quiet_margin_plan_spec (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) :
    let refined := weakQuietTracePlan (weakQuietReservePlan plan prices) prices
    WeakQuietGeometryPlanOK refined ∧ WeakQuietMarginPriceStatement refined prices ∧
    (∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      0 ≤ refined.coeffC R) ∧
    (∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      R.Kw + (A.Jw * A.Rw + 1) * (1 + A.Jw * A.Nw) ≤ refined.jetOrder R) ∧
    ((∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      A.Jw * A.Rw + 1 ≤ prices.depth R) → WeakQuietMarginDepthOK refined prices) := by
  refine ⟨weak_quiet_geometry_plan_of_threshold _ (fun R j =>
      (le_max_left _ _).trans (le_max_right _ _)),
    fun R => le_rfl, fun R => le_max_left _ _, ?_, ?_⟩
  · intro B A R
    exact (add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)) R.Kw).trans
      (Nat.le_max_right _ _)
  · intro hdepth B A R
    exact ⟨hdepth R,
      (add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_max_right _ _)) R.Kw).trans
        (Nat.le_max_right _ _)⟩

/-- Above the pre-cap drift threshold, the actual parent velocity supplies
native scalar evolution at every finite reserve and every sufficiently small
chosen radius. -/
theorem weak_quiet_parent_drift {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (hfloor : weakQuietDriftFloor B A.Λ ≤ c.M)
    (hcap : plan.radius R ≤ 1 / 2048) (i : ℕ) (hi : c.M < i) (a b : ℝ) (Q : ℕ) :
    Nonempty (WeakScalarTorusDrift (c.D.κ c.M) (plan.radius R * c.D.eps (i - 1)) a b
      (streamVel (c.D.Φ (i - 1))) Q) := by
  have hΛ : 128 ≤ A.Λ := (plan.base_ge B).trans c.base_ge
  rw [weakQuietDriftFloor, dite_eq_left hΛ] at hfloor
  have hh := (weak_parent_scalar_drift_budget B A.Λ hΛ).choose_spec.2 c.M hfloor
    (c.D.κ c.M) c.band.1 c.D.Φ c.streams i hi (plan.radius R) (plan.radius_pos R) hcap a b Q
  simpa only [OCData.eps, c.q_eq, c.base_eq] using hh

/-- All levels at or above the terminal weak level use the same diffusivity. -/
theorem weak_passage_kap_eq {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M ≤ i) : c.D.kap i = c.D.κ c.M := by
  unfold OCData.kap
  rw [c.terminal, Nat.min_eq_right hi]

/-- On the pinned quiet margin every level-i slow envelope vanishes, so the actual
stream and its parent agree as entire spatial functions. -/
theorem weak_middle_half_stream_eq {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hw : WeakQuietWindow c r i) (t : ℝ)
    (ht : t ∈ weakMiddleHalf c r i) : c.D.Φ i t = c.D.Φ (i - 1) t := by
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge)
  have hP : 0 < ocTauP c.D.α c.D.q c.D.Λ i := Velocity.Jets.ocTauP_pos hΛ
  obtain ⟨l, hl⟩ := hw.2.2.2.1
  have hquietMargin : t ∈ Set.Icc
      (((l : ℝ) + 1 / 2) * ocTauPP c.D.α c.D.q c.D.Λ i - ocTauP c.D.α c.D.q c.D.Λ i)
      (((l : ℝ) + 1 / 2) * ocTauPP c.D.α c.D.q c.D.Λ i + ocTauP c.D.α c.D.q c.D.Λ i) := by
    change r.tq i - ocTauP c.D.α c.D.q c.D.Λ i / 2 ≤ t ∧ t ≤ r.tq i at ht
    rw [← hl]
    constructor <;> linarith only [ht.1, ht.2, hP]
  obtain ⟨hprev, heq⟩ := c.streams.2 i (by omega)
  have heq' : c.D.Φ i = ocNextStream c.D.α c.D.q c.D.Λ c.D.ζ i (c.D.Φ (i - 1)) hprev := by
    simpa only [c.alpha, c.q_eq, c.base_eq, c.profile_eq] using heq
  rw [heq']
  funext x
  simp only [ocNextStream, CycleJointProofs.slowEnvelope_zero_on_renewal_quiet_margin hΛ l hquietMargin,
    zero_mul, tsum_zero, add_zero]

/-- The velocity identity used for parent-scale scalar smoothing. Its proof
uses the quiet margin, not a new assertion on the untrimmed quiet set. -/
theorem weak_middle_half_velocity_eq {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hw : WeakQuietWindow c r i) (t : ℝ)
    (ht : t ∈ weakMiddleHalf c r i) :
    streamVel (c.D.Φ i) t = streamVel (c.D.Φ (i - 1)) t := by
  unfold streamVel
  rw [weak_middle_half_stream_eq c r i hi hw t ht]

end AVRegularity.WeakEntryProofs.Assembly
end
end
