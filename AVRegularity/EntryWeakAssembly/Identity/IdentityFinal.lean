-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.Identity.IdentityB1Level
import AVRegularity.EntryTerminal.Ingredients.ForcedEnergy.TerminalForced
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Proofs.WeakGen.Reduction.PassageEnergy

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Identity

/-! **Identity B2: the plan-free constants of the lift from a level, and the level bound.**

`weak_lift_rep_from_at` has existential constants. They are fixed here once, by choice, as
definitions that do not read the plan (pattern of `Assembly/WeakReadoutBound.lean`):
`identityLiftBase`, `identityLiftSX`, `identityLiftSZ`, `identityLiftConst R` (the step constant
`C_st`), `identityLiftLevel R j₀`. `IdentityLiftPlanOK plan` says the floors of `plan` dominate
them. `identityB2_level_bound` is the bound of B1 with the profile bound from
`weak_readout_base_size` at the radius `min c 1`:

`‖s.W i t az‖_{C^s} ≤ 3 C_st^{M+J_w−i} C_B(n_i+3, min c 1) ε_{M+J_w}^{-(1+s)} ‖z‖_{c ε_i; π_i}`.

Special cases: `c ≥ 1` gives the base constant at radius `1`; a request below the lift-order
floors has the constant `0` by convention (no entry datum exists there). -/

open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.Providers.WeakGen.Readout

/-- The base floor of the lift from a level at the carrier `(1, 400)`. -/
def identityLiftBase (B : WeakCoefficientBase) : ℕ :=
  Classical.choose (Finite.WeakLift.weak_lift_rep_from_at B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq
    B.ζ B.hζ)

/-- The level tail of `weak_lift_rep_from_at` at the order `L_r = J_wN_w`, with the step constant
`Cst`, at a carrier index and a terminal level. -/
def IdentityLiftTail {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (Λ sX sZ : ℕ)
    (Cst : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData), D.α = B.α → D.q = B.q → D.Λ = Λ → D.ζ = B.ζ →
    IsOCStreamSeq B.α B.q Λ B.ζ D.Φ → IsOCBandChain B.α B.q Λ B.ζ M D.κ → D.term = M →
  ∀ (PW : ProvParams) (Dm : ℕ) (stage : ℕ → GenStage D ScalarH Dm A.bw j₀)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
    IsWeakConstruction D PW (⟨A.Nw, A.Rw, sX, sZ, A.η₀, M + A.Jw⟩ : WeakMenu) M A.Jw
      (D.termRW A.σw M) 0 stage →
    (∀ i, M < i → i ≤ M + A.Jw →
      IsWeakReadoutLifts i A.Nw (A.Jw * A.Rw) sX sZ (stage i) (CcR i)) →
    IsWeakReadoutChain M A.Jw A.Nw 0 A.η₀ (fun _ => A.Jw * A.Rw) stage CcR W →
  ∀ (m : ℕ), M ≤ m → m ≤ M + A.Jw →
  ∀ (t : ℝ) (g : CompIn (stage m).comps → Vec 2 → ℝ)
    (rT : Representation (CompSpace (stage m).comps)),
    IsRepresentationAt (D.eps m) (3 + (M + A.Jw - m) * A.Nw) rT →
    rT.value = compField (fun v => weakMass D A.Nw A.Jw A.η₀ v.1) (fun x v => g v x) →
  ∃ rW : Representation (CompSpace (stage (M + A.Jw)).comps),
    IsRepresentationAt (D.eps (M + A.Jw)) 3 rW ∧
    (∀ y, compReadoutCLM (fun v => weakMass D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) (rW.value y) =
      W m t g y) ∧
    representedSize B.s 3 (D.eps (M + A.Jw)) rW ≤
      ENNReal.ofReal (Cst ^ (M + A.Jw - m)) *
        representedSize B.s (3 + (M + A.Jw - m) * A.Nw) (D.eps m) rT

theorem identityLift_exists {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) :
    ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ → ∃ Cst : ℝ, 0 ≤ Cst ∧
      ∀ j₀ : ℕ, IsCarrierStart B.α B.q (max (identityLiftBase B) A.Λ) A.bw 1 400 j₀ →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        IdentityLiftTail A (max (identityLiftBase B) A.Λ) sX sZ Cst j₀ M :=
  (Classical.choose_spec (Finite.WeakLift.weak_lift_rep_from_at B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁
    B.q B.hq B.ζ B.hζ)).2 (max (identityLiftBase B) A.Λ) (le_max_left _ _) A.bw A.bw_pos
    A.bw_small A.Jw A.Nw A.Rw A.η₀ A.σw A.Jw_pos A.Nw_pos A.η₀_pos A.η₀_small A.σw_pos
    A.σw_small (A.Jw * A.Nw) le_rfl

/-- The floor of the slow lift order. -/
def identityLiftSX {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ :=
  (identityLift_exists A).choose

/-- The floor of the fast lift order. -/
def identityLiftSZ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ :=
  (identityLift_exists A).choose_spec.choose

theorem identityLift_spec {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (sX sZ : ℕ) (hX : identityLiftSX A ≤ sX) (hZ : identityLiftSZ A ≤ sZ) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧
      ∀ j₀ : ℕ, IsCarrierStart B.α B.q (max (identityLiftBase B) A.Λ) A.bw 1 400 j₀ →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        IdentityLiftTail A (max (identityLiftBase B) A.Λ) sX sZ Cst j₀ M :=
  (identityLift_exists A).choose_spec.choose_spec sX sZ hX hZ

open scoped Classical in
/-- The step constant `C_st` of the lift from a level at a request (`0` below the floors). -/
def identityLiftConst {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) : ℝ :=
  if h : identityLiftSX A ≤ R.sX ∧ identityLiftSZ A ≤ R.sZ then
    (identityLift_spec A R.sX R.sZ h.1 h.2).choose else 0

open scoped Classical in
/-- The level floor of the lift from a level at a request and a carrier index. -/
def identityLiftLevel {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (j₀ : ℕ) : ℕ :=
  if h : (identityLiftSX A ≤ R.sX ∧ identityLiftSZ A ≤ R.sZ) ∧
      IsCarrierStart B.α B.q (max (identityLiftBase B) A.Λ) A.bw 1 400 j₀ then
    ((identityLift_spec A R.sX R.sZ h.1.1 h.1.2).choose_spec.2 j₀ h.2).choose else 0

theorem identityLiftConst_nonneg {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) : 0 ≤ identityLiftConst R := by
  unfold identityLiftConst
  split_ifs with h
  · exact (identityLift_spec A R.sX R.sZ h.1 h.2).choose_spec.1
  · exact le_rfl

/-- The level tail of the lift from a level at the chosen constant, above the chosen floors. -/
theorem identityLift_tail {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (hX : identityLiftSX A ≤ R.sX) (hZ : identityLiftSZ A ≤ R.sZ)
    (j₀ : ℕ) (hcar : IsCarrierStart B.α B.q (max (identityLiftBase B) A.Λ) A.bw 1 400 j₀)
    (M : ℕ) (hM : identityLiftLevel R j₀ ≤ M) :
    IdentityLiftTail A (max (identityLiftBase B) A.Λ) R.sX R.sZ (identityLiftConst R) j₀ M := by
  have h1 : identityLiftSX A ≤ R.sX ∧ identityLiftSZ A ≤ R.sZ := ⟨hX, hZ⟩
  have hc : identityLiftConst R = (identityLift_spec A R.sX R.sZ h1.1 h1.2).choose :=
    dite_eq_left h1
  have hl : identityLiftLevel R j₀ =
      ((identityLift_spec A R.sX R.sZ h1.1 h1.2).choose_spec.2 j₀ hcar).choose :=
    dite_eq_left ⟨h1, hcar⟩
  rw [hc]
  exact ((identityLift_spec A R.sX R.sZ h1.1 h1.2).choose_spec.2 j₀ hcar).choose_spec M
    (hl ▸ hM)

/-- **The plan condition of the lift from a level**: the floors of the plan dominate the chosen
floors. -/
def IdentityLiftPlanOK (plan : WeakEntryGluePlan) : Prop :=
  (∀ B, identityLiftBase B ≤ plan.baseFloor B) ∧
  (∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B),
    identityLiftSX A ≤ plan.liftFloor A ∧ identityLiftSZ A ≤ plan.liftFloor A) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (j₀ : ℕ),
    identityLiftLevel R j₀ ≤ plan.levelFloor R C j₀

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x}

/-- **The lift from a level on the entry data**, at the chosen step constant. -/
theorem identityLevelLift_of_ok (hok : IdentityLiftPlanOK plan) (s : WeakEntrySchedule g) :
    IdentityLevelLift s (identityLiftConst R) := by
  obtain ⟨hbaseF, hliftF, hlev⟩ := hok
  have hmax : max (identityLiftBase B) A.Λ = A.Λ :=
    max_eq_right ((hbaseF B).trans x.base_ge)
  have htail := identityLift_tail R ((hliftF A).1.trans x.sX_ge) ((hliftF A).2.trans x.sZ_ge)
    x.j₀ (by rw [hmax]; exact x.carrier400) x.M ((hlev R C x.j₀).trans x.level_ge)
  rw [hmax] at htail
  intro m hm hmt t a rT hrT hval
  exact htail x.D x.alpha x.q_eq x.base_eq x.profile_eq x.streams x.band x.terminal x.P x.Dm
    g.stage s.CcR s.W g.construction s.lifts s.chain m hm hmt t a rT hrT hval

/-- **The profile bound at the stage `i`** from the proved base size, at the radius `c ∈ (0, 1]`. -/
theorem identityLevelProfile_of_base (i : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    IdentityLevelProfile x g i c
      (weakReadoutBaseConst weak_readout_base_size B.s ((x.M + A.Jw - i) * A.Nw + 3) c) := by
  have hCBdef : weakReadoutBaseConst weak_readout_base_size B.s ((x.M + A.Jw - i) * A.Nw + 3) c =
      (weak_readout_base_size B.s ((x.M + A.Jw - i) * A.Nw + 3) c hc hc1).choose :=
    dite_eq_left ⟨hc, hc1⟩
  obtain ⟨_, hsize⟩ :=
    (weak_readout_base_size B.s ((x.M + A.Jw - i) * A.Nw + 3) c hc hc1).choose_spec
  rw [← hCBdef] at hsize
  intro e he he1 z az haz
  exact hsize (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
    (fun v => weakEntry_mass_pos g v.1) e he he1 z az haz

theorem identityBaseConst_nonneg {c : ℝ} (n : ℕ) :
    0 ≤ weakReadoutBaseConst weak_readout_base_size B.s n c := by
  unfold weakReadoutBaseConst
  split_ifs with h
  · exact (weak_readout_base_size B.s n c h.1 h.2).choose_spec.1
  · exact le_rfl

/-- The constant of the level with `j = M + J_w − i` steps to go, at the radius `c`. -/
def identityLevelConst (B : WeakCoefficientBase) {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (c : ℝ) (j : ℕ) : ℝ :=
  3 * (identityLiftConst R ^ j *
    weakReadoutBaseConst weak_readout_base_size B.s (j * A.Nw + 3) (min c 1))

theorem identityLevelConst_nonneg (R : WeakPassageRequest A) (c : ℝ) (j : ℕ) :
    0 ≤ identityLevelConst B R c j :=
  mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg (identityLiftConst_nonneg R) _)
    (identityBaseConst_nonneg _))

/-- **The level bound** (B1 to B3): the readout of a classical field of the stage `i`, at any
radius `c > 0`. -/
theorem identityB2_level_bound (hok : IdentityLiftPlanOK plan) (s : WeakEntrySchedule g)
    {c : ℝ} (hc : 0 < c) {i : ℕ} (hMi : x.M ≤ i) (hi : i ≤ x.M + A.Jw) (t : ℝ)
    (z : ∀ v : CompIn (g.stage i).comps,
      TorusHk ((x.M + A.Jw - i) * A.Nw + 5) (ScalarH v.1.root))
    (az : CompIn (g.stage i).comps → Vec 2 → ℝ)
    (haz : ∀ v, IsClassicalRep (z v) (az v) ((x.M + A.Jw - i) * A.Nw + 3)) :
    CsNormLe B.s (s.W i t az)
      (identityLevelConst B R c (x.M + A.Jw - i) * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
        weightedNorm (c * x.D.eps i)
          (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) z) := by
  have hc' : 0 < min c 1 := lt_min hc one_pos
  have h1 := identityB1_level_bound s (identityLiftConst_nonneg R)
    (identityBaseConst_nonneg _) (identityLevelLift_of_ok hok s) hMi hi
    (identityLevelProfile_of_base (x := x) (g := g) i hc' (min_le_right _ _)) t z az haz
  refine Applications.csNormLe_mono h1 ?_
  have hmono : weightedNorm (min c 1 * x.D.eps i)
        (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) z ≤
      weightedNorm (c * x.D.eps i)
        (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) z := by
    have hΛ1 : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans x.base128
    have he : 0 < x.D.eps i := Construction.Stream.ocEpsilon_pos hΛ1
    have := EntryTerminal.Route.sqrt_massNormSq_mono_radius
      (S := fun v : CompIn (g.stage i).comps => ScalarH v.1.root)
      (k := (x.M + A.Jw - i) * A.Nw + 5) (min c 1 * x.D.eps i) (c * x.D.eps i)
      (mul_nonneg hc'.le he.le) (mul_le_mul_of_nonneg_right (min_le_left _ _) he.le)
      (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
      (fun v => weakEntry_mass_pos g v.1) z
    simpa [weightedNorm] using this
  have hpow : 0 ≤ x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) := by
    have hΛ1 : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans x.base128
    exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _
  unfold identityLevelConst
  exact mul_le_mul_of_nonneg_left hmono (mul_nonneg (mul_nonneg (by norm_num)
    (mul_nonneg (pow_nonneg (identityLiftConst_nonneg R) _) (identityBaseConst_nonneg _))) hpow)

end AVRegularity.WeakEntryProofs.Identity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Identity

/-! **Identity C4a: the plan condition, the constants and the bound of one telescoped level.**

* `IdentityPlanOK plan pp`: every plan condition of the weak identity (the lead collects them):
  linearity floor, readout-bound plan condition, lift-from-a-level floors, the floors of the
  passage plan `pp` below those of `plan`, level floor `≥ 1`, the moment floor
  (`P_w + 2 q^{J_w} ≤ σ_w L`, so that `ε_{M+J_w}^{-(1+s)} ε_M^{χ_w+σ_wL} ≤ 4 ε_M^{P_w}`), and
  `identityCidConst ≤ C_id`.
* `identityC4_level_bound`: for `M < i ≤ M + J_w` and `t ≥ tq (M+1)` in the window,
  `‖W_i (aU_i − Λ_i𝓡_i aU_{i−1})‖_{C^s} ≤ K_{M+J_w−i} · 4 ε_M^{P_w} · (E |F| Φ)`, with `K_j` the level
  constants of B, `E`, `F` the energy and force constants of `pp`, `Φ` the mass constant.

Special cases: `f = 0` gives `Φ = 0` and the bound `0`. -/

open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.Providers.WeakGen.Comparison
  AVRegularity.Providers.WeakGen.Readout AVRegularity.WeakEntryProofs.ReadoutLinear
  AVRegularity.Construction.Preservation.FullLift AVRegularity.CycleComparison.Reconstruction

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x} {s : WeakEntrySchedule g}
  {θ : ℝ → Vec 2 → ℝ}

/-- The coefficient of `‖f‖₂` in the mass constant. -/
def identityMassCoef (plan : WeakEntryGluePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) : ℝ :=
  Real.sqrt (2 * max 1 (weakEntryPassageConst plan R C 0 * weakEntryQuietConst plan R C 0) ^ A.Jw)

theorem identityMassConst_eq (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (f : Vec 2 → ℝ) :
    identityMassConst plan R C f = identityMassCoef plan R C * Real.sqrt (l2NormSq f) :=
  Real.sqrt_mul (mul_nonneg (by norm_num) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _))
    _

/-- The sum of the level constants of B over the `J_w` levels of the telescoping sum. -/
def identityKsum (B : WeakCoefficientBase) {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (c : ℝ) : ℝ :=
  ∑ j ∈ Finset.range A.Jw, identityLevelConst B R c (A.Jw - 1 - j)

/-- **The constant of the identity**: `4 E |F| c_Φ K_sum + 4 |C_read| |C_K|`. -/
def identityCidConst (plan : WeakEntryGluePlan) (pp : WeakPassagePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) : ℝ :=
  4 * pp.energyC R * |pp.forceC R| * identityMassCoef plan R C * identityKsum B R (pp.radius R) +
    4 * |plan.Cread R C| * |plan.CK R C|

/-- **The plan condition of the weak identity.** -/
structure IdentityPlanOK (plan : WeakEntryGluePlan) (pp : WeakPassagePlan) : Prop where
  linear : WeakReadoutLinearPlanOK plan
  read : WeakReadoutBoundPlanOK weak_readout_base_size plan
  lift : IdentityLiftPlanOK plan
  base_pp : ∀ B, pp.baseFloor B ≤ plan.baseFloor B
  moment_pp : ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B),
    pp.momentFloor A ≤ plan.momentFloor A
  level_pp : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (j : ℕ), pp.levelFloor R j ≤ plan.levelFloor R C j
  lift_pp : ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B),
    pp.liftFloor A ≤ plan.liftFloor A
  level_pos : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (j₀ : ℕ), 1 ≤ plan.levelFloor R C j₀
  moment_exp : ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (L : ℕ),
    plan.momentFloor A ≤ L → A.Pw + 2 * B.q ^ A.Jw ≤ A.σw * L
  Cid : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)), identityCidConst plan pp R C ≤ plan.Cid R C

/-- For `t ≥ tq (M+1)` in the window, `t` lies in the window of every level. -/
theorem identityC4_window (s : WeakEntrySchedule g) {t : ℝ} (ht : s.tq (x.M + 1) ≤ t)
    {i : ℕ} (hlo : x.M + 1 ≤ i) (hhi : i ≤ x.M + A.Jw + 1) : s.tq i ≤ t :=
  (identityC1_tq_le s hlo hhi).trans ht

/-- **The bound of one telescoped level.** -/
theorem identityC4_level_bound (pp : WeakPassagePlan) (h : IdentityPlanOK plan pp)
    (hcommon : WeakEntryCommonOK plan) (hA : WeakEntryPassageEnergyStatement plan)
    (hB : WeakEntryQuietTraceHighStatement plan) (hI1 : WeakPassageComparisonHighStatement pp)
    (f : Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (red : WeakEntryReduced s θ) {i : ℕ} (hMi : x.M < i) (hi : i ≤ x.M + A.Jw)
    (hok : IdentityLiftOK red i) {t : ℝ} (ht1 : s.tq (x.M + 1) ≤ t) (ht2 : t ≤ x.a + A.T₀) :
    CsNormLe B.s
      (s.W i t (fun v y => identityAU red i t v y - identityLift red i t v y))
      (identityLevelConst B R (pp.radius R) (x.M + A.Jw - i) *
        (4 * x.D.eps x.M ^ A.Pw *
          (pp.energyC R * |pp.forceC R| * identityMassConst plan R C f))) := by
  have hLw := identityC1_Nw_le x
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans x.base128
  have hmass : ∀ t' ∈ Set.Icc (s.tq (i + 1)) (x.a + A.T₀),
      weightedNorm 1 (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
        (fun _ => 1) (fun v => truncateTorusHk (Nat.zero_le R.Kw) (red.Ur i v t')) ≤
        identityMassConst plan R C f := fun t' ht' =>
    identityA4_mass_bound hcommon hA hB s f θ hθ red i hMi hi t' ht'
  obtain ⟨ehi, hrep, hen⟩ := identityA7_errors pp (h.base_pp B) (h.moment_pp A) (h.level_pp R C)
    (h.lift_pp A) hI1 hθ red hLw i hMi hi hok hmass
  have htw : t ∈ Set.Icc (s.tq i) (x.a + A.T₀) :=
    ⟨identityC4_window s ht1 (by omega) (by omega), ht2⟩
  have hlev := identityB2_level_bound h.lift s (pp.radius_pos R) hMi.le hi t (fun v => ehi v t)
    (fun v y => identityAU red i t v y - identityLift red i t v y) (fun v => hrep t htw v)
  have hen' := hen t htw
  set Φ := identityMassConst plan R C f with hΦ
  have hΦ0 : 0 ≤ Φ := Real.sqrt_nonneg _
  have hεM : 0 ≤ x.D.eps x.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) :=
    Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _
  have hF0 : 0 ≤ |pp.forceC R| * x.D.eps x.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) * Φ :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hεM) hΦ0
  have hE0 := pp.energyC_nonneg R
  have hwn : weightedNorm (pp.radius R * x.D.eps i)
      (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
      (fun v => ehi v t) ≤
      pp.energyC R * (|pp.forceC R| * x.D.eps x.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) * Φ) := by
    unfold weightedNorm massNormSq
    simp only [one_pow, div_one]
    refine (Real.sqrt_le_sqrt hen').trans ?_
    rw [Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg hE0, abs_mul, abs_mul, abs_of_nonneg hεM,
      abs_of_nonneg hΦ0]
  have hKn := identityLevelConst_nonneg (B := B) R (pp.radius R) (x.M + A.Jw - i)
  have hpow : 0 ≤ x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) :=
    Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _
  refine Applications.csNormLe_mono hlev ?_
  have hM1 : 1 ≤ x.M := le_trans (h.level_pos R C x.j₀) x.level_ge
  have hq : 1 < x.D.q := by rw [x.q_eq]; exact B.hq.1
  have hs1 : B.s < 1 := by have h1 := B.hs₁; have h2 := B.hα₀; linarith
  have hexp := identityC2_main hq hΛ1 hM1 B.hs₀ hs1 A.Jw
    (E := A.Pw + 2 * B.q ^ A.Jw + 1) (P := A.Pw) (by rw [x.q_eq]; linarith)
  have hqeq : ∀ n, x.D.eps n = ocEpsilon x.D.q x.D.Λ n := fun n => rfl
  have h1 : x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) * x.D.eps x.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) ≤
      4 * x.D.eps x.M ^ A.Pw := by
    simp only [hqeq]
    rw [x.q_eq] at *
    simpa using hexp
  calc identityLevelConst B R (pp.radius R) (x.M + A.Jw - i) *
        x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
        weightedNorm (pp.radius R * x.D.eps i)
          (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
          (fun v => ehi v t)
      ≤ identityLevelConst B R (pp.radius R) (x.M + A.Jw - i) *
        x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
        (pp.energyC R * (|pp.forceC R| * x.D.eps x.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) * Φ)) :=
        mul_le_mul_of_nonneg_left hwn (mul_nonneg hKn hpow)
    _ = identityLevelConst B R (pp.radius R) (x.M + A.Jw - i) *
        ((x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) * x.D.eps x.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1)) *
          (pp.energyC R * |pp.forceC R| * Φ)) := by ring
    _ ≤ identityLevelConst B R (pp.radius R) (x.M + A.Jw - i) *
        ((4 * x.D.eps x.M ^ A.Pw) * (pp.energyC R * |pp.forceC R| * Φ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hKn
        exact mul_le_mul_of_nonneg_right h1
          (mul_nonneg (mul_nonneg hE0 (abs_nonneg _)) hΦ0)

end AVRegularity.WeakEntryProofs.Identity
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Identity

/-! **The weak identity** `weak_readout_identity : WeakReadoutIdentityStatement plan`.

Conditional on: the plan condition `IdentityPlanOK plan pp`, the common plan condition and the
passage energy and quiet trace bounds (`hcommon`, `hA`, `hB`; each is a theorem under its own plan condition), the
comparison `WeakPassageComparisonHighStatement pp` and
`IdentityLiftAllStatement plan` (the smoothness and periodicity of the glued lifts).

Special cases: `f = 0` gives every term `0`; `J_w = 1` has one telescoped level. -/

section
open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.Providers.WeakGen.Comparison

/-- Smoothness and periodicity of the glued lifts at every level of every reduction. -/
def IdentityLiftAllStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    {g : WeakEntryStages x} {s : WeakEntrySchedule g} {θ : ℝ → Vec 2 → ℝ}
    (red : WeakEntryReduced s θ) (i : ℕ), x.M < i → i ≤ x.M + A.Jw → IdentityLiftOK red i

theorem identityC5_csNormLe_sum {ι : Type*} (s : ℝ) (S : Finset ι) (F : ι → Vec 2 → ℝ)
    (K : ι → ℝ) (h : ∀ j ∈ S, CsNormLe s (F j) (K j)) :
    CsNormLe s (fun y => ∑ j ∈ S, F j y) (∑ j ∈ S, K j) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro x y z _; simp
  | insert a S ha ih =>
    have h1 := Finite.Assembly.csNormLe_add (h a (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert ha] using h1

/-- **The weak identity**. -/
theorem weak_readout_identity (plan : WeakEntryGluePlan) (pp : WeakPassagePlan)
    (h : IdentityPlanOK plan pp) (hcommon : WeakEntryCommonOK plan)
    (hA : WeakEntryPassageEnergyStatement plan) (hB : WeakEntryQuietTraceHighStatement plan)
    (hI1 : WeakPassageComparisonHighStatement pp) (hlift : IdentityLiftAllStatement plan) :
    WeakReadoutIdentityStatement plan := by
  intro B A R C x g s law hm hr f θ hθ red p hp t ht aV haV
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans x.base128
  have ht1 : s.tq (x.M + 1) ≤ t := s.finish.trans ht.1
  have ht2 : t ≤ x.a + A.T₀ := ht.2
  refine ⟨identityTheta red t, identityTheta_periodic red t,
    identityTheta_ae red ⟨identityC4_window s ht1 (by omega) le_rfl, ht2⟩, ?_⟩
  -- decomposition
  have hsum := identityC1_sum h.linear red (fun i h1 h2 => hlift red i h1 h2)
    (fun i h1 h2 => ⟨identityC4_window s ht1 (by omega) (by omega), ht2⟩) A.Jw le_rfl
  have hlast := identityC3_last h.read h.linear law hm hr f red p hp ⟨ht1, ht2⟩ aV haV
  have hlev : ∀ j ∈ Finset.range A.Jw, CsNormLe B.s
      (fun y => s.W (x.M + j + 1) t (fun v y' => identityAU red (x.M + j + 1) t v y' -
        identityLift red (x.M + j + 1) t v y') y)
      (identityLevelConst B R (pp.radius R) (A.Jw - 1 - j) *
        (4 * x.D.eps x.M ^ A.Pw *
          (pp.energyC R * |pp.forceC R| * identityMassConst plan R C f))) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have := identityC4_level_bound pp h hcommon hA hB hI1 f hθ red (i := x.M + j + 1)
      (by omega) (by omega) (hlift red _ (by omega) (by omega)) ht1 ht2
    have e : x.M + A.Jw - (x.M + j + 1) = A.Jw - 1 - j := by omega
    rw [e] at this
    exact this
  have hS := identityC5_csNormLe_sum B.s _ _ _ hlev
  have hadd := Finite.Assembly.csNormLe_add hS hlast
  have heq : (fun y => identityTheta red t y - weakEntryReadoutMap s t aV y) =
      fun y => (∑ j ∈ Finset.range A.Jw, s.W (x.M + j + 1) t
        (fun v y' => identityAU red (x.M + j + 1) t v y' - identityLift red (x.M + j + 1) t v y') y) +
      (s.W x.M t (identityAU red x.M t) y - weakEntryReadoutMap s t aV y) := by
    funext y
    rw [identityTheta_eq_W, ← hsum y]
    ring
  rw [heq]
  refine Applications.csNormLe_mono hadd ?_
  -- constants
  have hM1 : 1 ≤ x.M := le_trans (h.level_pos R C x.j₀) x.level_ge
  have hq : 1 < x.D.q := by rw [x.q_eq]; exact B.hq.1
  have hs1 : B.s < 1 := by have h1 := B.hs₁; have h2 := B.hα₀; linarith
  have hχ : 0 < weakChi B.α B.q A.η₀ := weakChi_pos B.hα₀ B.hq.1 B.hq.2.1 A.η₀_small
  have hexp := identityC2_main hq hΛ1 hM1 B.hs₀ hs1 A.Jw
    (E := weakChi B.α B.q A.η₀ + A.σw * R.L) (P := A.Pw)
    (by rw [x.q_eq]; have := h.moment_exp A R.L x.moment_ge; linarith)
  have h1 : x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
      x.D.eps x.M ^ (weakChi B.α B.q A.η₀ + A.σw * R.L) ≤ 4 * x.D.eps x.M ^ A.Pw := by
    have hqeq : ∀ n, x.D.eps n = ocEpsilon x.D.q x.D.Λ n := fun n => rfl
    simp only [hqeq]
    rw [x.q_eq] at *
    simpa using hexp
  have hsq := Real.sqrt_nonneg (l2NormSq f)
  have hpw : 0 ≤ x.D.eps x.M ^ A.Pw :=
    Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _
  have hCid := h.Cid R C
  have hlast_le : |plan.Cread R C| * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
      (|plan.CK R C| * x.D.eps x.M ^ (weakChi B.α B.q A.η₀ + A.σw * R.L) *
        Real.sqrt (l2NormSq f)) ≤
      |plan.Cread R C| * |plan.CK R C| * Real.sqrt (l2NormSq f) * (4 * x.D.eps x.M ^ A.Pw) := by
    calc _ = |plan.Cread R C| * |plan.CK R C| * Real.sqrt (l2NormSq f) *
          (x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
            x.D.eps x.M ^ (weakChi B.α B.q A.η₀ + A.σw * R.L)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1
          (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hsq)
  have key : identityKsum B R (pp.radius R) *
        (4 * x.D.eps x.M ^ A.Pw *
          (pp.energyC R * |pp.forceC R| * identityMassConst plan R C f)) +
      |plan.Cread R C| * |plan.CK R C| * Real.sqrt (l2NormSq f) * (4 * x.D.eps x.M ^ A.Pw) ≤
      plan.Cid R C * x.D.eps x.M ^ A.Pw * Real.sqrt (l2NormSq f) := by
    have heq2 : identityKsum B R (pp.radius R) *
        (4 * x.D.eps x.M ^ A.Pw *
          (pp.energyC R * |pp.forceC R| * identityMassConst plan R C f)) +
      |plan.Cread R C| * |plan.CK R C| * Real.sqrt (l2NormSq f) * (4 * x.D.eps x.M ^ A.Pw) =
      identityCidConst plan pp R C * x.D.eps x.M ^ A.Pw * Real.sqrt (l2NormSq f) := by
      rw [identityMassConst_eq]
      unfold identityCidConst
      ring
    rw [heq2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCid hpw) hsq
  refine le_trans (add_le_add (le_of_eq ?_) hlast_le) key
  unfold identityKsum
  rw [Finset.sum_mul]
end

/-! **Identity lift: `IdentityLiftOK` from the smoothness of `readoutLinear_lift_contDiff` and the
plan condition for periodicity.**

Plan condition for the smoothness: `L_w + 3 ≤ plan.liftFloor A` for every `A`
(`IdentityLiftFloorOK`). Periodicity comes from `weakEntry_gluedLift_periodic` under `WeakEntrySlotLiftPlanOK plan`, so
`weak_readout_identity_of_plan` is conditional on the comparison, the passage energy, the quiet trace bound and the plan conditions only. -/

section
open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.Providers.WeakGen.Comparison
  AVRegularity.WeakEntryProofs.ReadoutLinear

/-- The lift-order floor of the plan is at least `L_w + 3`. -/
def IdentityLiftFloorOK (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B), A.Lw + 3 ≤ plan.liftFloor A

theorem identityReadoutStep_periodic {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (i : ℕ) (η₀ : ℝ)
    (G G' : GenStage D ScalarH Dm b j₀) (g : CompIn G'.comps → Vec 2 → ℝ)
    (hg : ∀ v, IsZ2Periodic (g v)) (v : CompIn G.comps) :
    IsZ2Periodic (weakReadoutStep i η₀ G G' g v) := by
  intro n y
  classical
  show (∑ v' : CompIn G'.comps, if compParent i v'.1 = v.1 then
      (D.eps (i - 1) ^ η₀) ^ (compWord i v'.1).length * g v' (y + latticeShift n) else 0) = _
  refine Finset.sum_congr rfl fun v' _ => ?_
  rw [hg v' n y]

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x} {s : WeakEntrySchedule g}
  {θ : ℝ → Vec 2 → ℝ}

theorem identityLift_step_contDiff (red : WeakEntryReduced s θ) (i : ℕ) (t : ℝ)
    (hLw : A.Nw ≤ A.Lw) (w : CompIn (g.stage i).comps) :
    ContDiff ℝ (((A.Lw + 3 - A.Nw + A.Nw : ℕ)) : ℕ∞)
      (weakReadoutStep i A.η₀ (g.stage i) (g.stage (i - 1)) (identityAU red (i - 1) t) w) := by
  have hr : A.Lw + 3 - A.Nw + A.Nw = A.Lw + 3 := by omega
  rw [hr]
  exact readoutLinear_step_contDiff _ _ _ _ _ (fun w => (identityAU_rep red (i - 1) t w).2.1) w

theorem identityLift_smooth (hfa : A.Lw + 3 ≤ plan.liftFloor A) (red : WeakEntryReduced s θ)
    {i : ℕ} (hMi : x.M < i) (hi : i ≤ x.M + A.Jw) (t : ℝ) (v : CompIn (g.stage i).comps) :
    ContDiff ℝ ((A.Lw + 3 - A.Nw : ℕ) : ℕ∞) (identityLift red i t v) := by
  have hLw := identityC1_Nw_le x
  have hcN := readoutLinear_cell_pos (x := x) i
  have hτ := readoutLinear_tau_pos (x := x) i
  have hX : A.Lw + 3 - A.Nw ≤ R.sX :=
    (by omega : A.Lw + 3 - A.Nw ≤ A.Lw + 3).trans (hfa.trans x.sX_ge)
  have hZ : A.Lw + 3 - A.Nw ≤ R.sZ :=
    (by omega : A.Lw + 3 - A.Nw ≤ A.Lw + 3).trans (hfa.trans x.sZ_ge)
  exact readoutLinear_lift_contDiff (g.stage i) i A.Nw (A.Jw * A.Rw) (s.CcR i) t
    (A.Lw + 3 - A.Nw) hcN hτ (s.lifts i hMi hi) hX hZ
    (weakReadoutStep i A.η₀ (g.stage i) (g.stage (i - 1)) (identityAU red (i - 1) t))
    (fun w => identityLift_step_contDiff red i t hLw w) v

theorem identityLift_periodic (hpk : WeakEntrySlotLiftPlanOK plan) (red : WeakEntryReduced s θ)
    {i : ℕ} (hMi : x.M < i) (hi : i ≤ x.M + A.Jw) (t : ℝ) (v : CompIn (g.stage i).comps) :
    IsZ2Periodic (identityLift red i t v) :=
  weakEntry_gluedLift_periodic hpk g s hMi hi t
    (weakReadoutStep i A.η₀ (g.stage i) (g.stage (i - 1)) (identityAU red (i - 1) t))
    (identityReadoutStep_periodic i A.η₀ (g.stage i) (g.stage (i - 1)) (identityAU red (i - 1) t)
      (fun w => (identityAU_rep red (i - 1) t w).2.2.1)) v

theorem identityLiftAll_of (plan : WeakEntryGluePlan) (hfl : IdentityLiftFloorOK plan)
    (hpk : WeakEntrySlotLiftPlanOK plan) : IdentityLiftAllStatement plan := by
  intro B A R C x g s θ red i hMi hi t _ v
  exact ⟨identityLift_smooth (hfl A) red hMi hi t v, identityLift_periodic hpk red hMi hi t v⟩

/-- **The weak identity**, conditional on the comparison, the passage energy, the quiet trace bound and the plan conditions. -/
theorem weak_readout_identity_of_plan (plan : WeakEntryGluePlan) (pp : WeakPassagePlan)
    (h : IdentityPlanOK plan pp) (hfl : IdentityLiftFloorOK plan)
    (hpk : WeakEntrySlotLiftPlanOK plan)
    (hcommon : WeakEntryCommonOK plan)
    (hA : WeakEntryPassageEnergyStatement plan) (hB : WeakEntryQuietTraceHighStatement plan)
    (hI1 : WeakPassageComparisonHighStatement pp) :
    WeakReadoutIdentityStatement plan :=
  weak_readout_identity plan pp h hcommon hA hB hI1 (identityLiftAll_of plan hfl hpk)
end

end AVRegularity.WeakEntryProofs.Identity
end

section
namespace AVRegularity.WeakEntryProofs.Identity

/-! **The weak readout identity, final form.**

`WeakReadoutIdentityPlanOK plan pp` bundles every plan condition of the identity. With it,
`weak_readout_identity_final` has the comparison statement as its only other
hypothesis; the passage energy and quiet trace bounds (and the common condition) are discharged by their proved theorems. -/

open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.Providers.WeakGen.Comparison

/-- All plan conditions of the weak readout identity. -/
structure WeakReadoutIdentityPlanOK (plan : WeakEntryGluePlan) (pp : WeakPassagePlan) : Prop where
  identity : IdentityPlanOK plan pp
  liftFloor : IdentityLiftFloorOK plan
  slotLifts : WeakEntrySlotLiftPlanOK plan
  common : WeakEntryCommonOK plan
  passageEnergy : WeakEntryPassageEnergyPlanOK plan
  quietTrace : WeakEntryQuietTraceHighPlanOK plan

/-- **The weak readout identity**: the only non-plan hypothesis is the comparison statement. -/
theorem weak_readout_identity_final (plan : WeakEntryGluePlan) (pp : WeakPassagePlan)
    (hok : WeakReadoutIdentityPlanOK plan pp) (hI1 : WeakPassageComparisonHighStatement pp) :
    WeakReadoutIdentityStatement plan :=
  weak_readout_identity_of_plan plan pp hok.identity hok.liftFloor hok.slotLifts hok.common
    (weakEntryPassageEnergy hok.common hok.passageEnergy)
    (weak_entry_quiet_trace_high hok.common hok.quietTrace) hI1

end AVRegularity.WeakEntryProofs.Identity
end
end
end
