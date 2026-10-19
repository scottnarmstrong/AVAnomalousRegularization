-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Assembly.WeakCommonCase
import AVRegularity.CycleReference.FluxFastDiscrepancy

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Composition of the coefficient, quiet-trace and comparison statements. Four
explicit glue obligations retain the datum-independent clock, the complete raw
trace, the paired solve and the representative-valued readout identity. -/

/-- Clock and readout: a datum-independent clock and actual readout lifts/chain.
The cutoff/window uniqueness route supplies lifts; cascade waiting supplies the clock. -/
def WeakEntryScheduleStatement (plan : WeakEntryGluePlan) : Prop :=
  WeakEntryCommonOK plan →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)}, 400 ≤ C.Υ →
    ∀ (x : WeakEntryData plan C) (g : WeakEntryStages x), Nonempty (WeakEntrySchedule g)

/-- Raw solution: solve all unregularized triangular passages from the whole incoming
trace, using descending derivative reserves and uniqueness when reserves grow. -/
def WeakEntryReductionStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
    IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ →
    Nonempty (WeakEntryReduced s θ)

/-- The paired claim for a supplied reduction. The raw trajectory and full trace
are fixed expressions, never existentially replaced by a homogeneous root row. -/
def WeakEntryPairBounds {plan : WeakEntryGluePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    {g : WeakEntryStages x} {s : WeakEntrySchedule g} {θ : ℝ → Vec 2 → ℝ}
    (r : WeakEntryReduced s θ) (law : BirthLaw) (f : Vec 2 → ℝ) (p : WeakEntryPair (g := g)) : Prop :=
  IsWeakPaired x.P A.φ₀ A.hφ₀ law x.M R.Kw R.L R.nW x.a A.T₀ A.σw
    (weakChi B.α B.q A.η₀) (plan.radius R) (plan.CK R C) f g.Gw (s.tq (x.M + 1))
    (fun v => rerootFamily g.relabel (r.Ur x.M) v (s.tq (x.M + 1)))
    (rerootFamily g.relabel (r.Ur x.M)) p.V p.Uw p.Vw p.Uk p.Vk

/-- Paired claim: iterate the quiet traces, prove raw energy, then solve with the
paired kernel from the same complete trace and estimate moment cancellation.
The common plan must include the quiet thresholds and select a sufficiently small
radius before the coefficient call. No shrinking of an already certified stage occurs. -/
def WeakEntryPairStatement (plan : WeakEntryGluePlan) : Prop :=
  WeakPassageQuietTraceAt 1 400 →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g)
    (law : BirthLaw), law.rootMass = g.rootM → law.rootReadout = g.rootR →
  ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
    IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ →
  ∀ r : WeakEntryReduced s θ, ∃ p : WeakEntryPair (g := g), WeakEntryPairBounds r law f p

/-- Readout: scaled Fourier readout and telescoping of comparison errors plus
the paired difference, using the periodic continuous representative of theta.
Comparison thresholds, moment and readout orders belong to the same pre-data plan. -/
def WeakEntryReadoutStatement (plan : WeakEntryGluePlan) : Prop :=
  WeakPassageComparisonAt 1 400 →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g)
    (law : BirthLaw), law.rootMass = g.rootM → law.rootReadout = g.rootR →
  ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
    IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ →
  ∀ (r : WeakEntryReduced s θ) (p : WeakEntryPair (g := g)), WeakEntryPairBounds r law f p →
    IsWeakReadout law x.M A.Jw A.Lw R.Kw (x.D.κ x.M) x.a A.τ A.T₀ B.s A.Pw
      (plan.radius R) (plan.Cread R C) (plan.Cid R C) f θ g.Gw
      (fun t z y => s.W x.M t (fun v y' => z (g.relabel v) y') y) p.V

/-- Exact weak entry. The radius choice precedes `entry_coefficients`;
the stage invariant is taken from that statement at precisely this radius. -/
theorem entry_weak_of_ingredients (hcoeff : EntryCoefficientsStatement)
    (hquiet : WeakPassageQuietTraceAt 1 400) (hcompare : WeakPassageComparisonAt 1 400)
    (plan : WeakEntryGluePlan) (hcommon : WeakEntryCommonOK plan)
    (hschedule : WeakEntryScheduleStatement plan)
    (hreduce : WeakEntryReductionStatement plan) (hpair : WeakEntryPairStatement plan)
    (hreadout : WeakEntryReadoutStatement plan) : EntryWeakStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let B : WeakCoefficientBase := ⟨α, s, hα₀, hα₁, hs₀, hs₁, q, hq, ζ, hζ⟩
  obtain ⟨Λc, hΛc, hcoeff⟩ := hcoeff α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max Λc (plan.baseFloor B), hΛc.trans (Nat.le_max_left _ _), ?_⟩
  intro Λ hΛ φ₀ hφ₀ hsm hnn hmass hsupp bw hbw hbwsmall Jw τ T₀ Pw η₀ hJ hτ hτT hP hη hηsmall
  let A₀ : WeakEntryPhysical B :=
    ⟨Λ, φ₀, hφ₀, hsm, hnn, hmass, hsupp, bw, hbw, hbwsmall, Jw, τ, T₀, Pw, η₀,
      hJ, hτ, hτT, hP, hη, hηsmall⟩
  let o := weakEntryOrdersChoice A₀
  refine ⟨o.N, o.R, o.L, o.N_pos, o.L_eq, o.order_N, o.order_R, ?_⟩
  intro σw hσ hσsmall
  let A := A₀.withOrders o σw hσ hσsmall
  obtain ⟨Lc, hcoeff⟩ := hcoeff Λ ((Nat.le_max_left _ _).trans hΛ)
    φ₀ hφ₀ hsm hnn hmass hsupp bw hbw hbwsmall Jw τ T₀ Pw η₀ hJ hτ hτT hP hη hηsmall
    o.N o.R o.L o.N_pos o.L_le σw hσ hσsmall
  refine ⟨max Lc (plan.momentFloor A), plan.liftFloor A, plan.liftFloor A, ?_⟩
  intro L Kw sX sZ nW kReq hG hL hSX hSZ hn hK
  let R : WeakPassageRequest A := ⟨L, Kw, sX, sZ, nW, kReq, hG, hn, hK⟩
  let cK := plan.radius R
  have hcK := weak_entry_radius_spec (plan.radiusBudget R)
  obtain ⟨_CK, CL, Cχ, _Cread, _Cid, kW, hradius, halloc, CH, Υ, hCH, hΥ, hcoeff⟩ :=
    hcoeff L Kw sX sZ nW kReq hG ((Nat.le_max_left _ _).trans hL) hn hK
      cK hcK.1 hcK.2.1
  -- one carrier start at the maxima gives those of the coefficient statement and of the passages
  let CHw := max CH 1
  let Υw := max Υ 400
  let C : WeakEntryAllocation R cK :=
    ⟨CL, Cχ, kW, hradius, halloc, CHw, Υw, le_max_right _ _, hΥ.trans_le (le_max_left _ _)⟩
  refine ⟨cK, plan.CK R C, CL, Cχ, plan.Cread R C, plan.Cid R C, kW,
    hcK.1, hradius, halloc, CHw, Υw, le_max_right _ _,
    hΥ.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hcarrier
  have hΛ1 : 1 ≤ Λ := (by norm_num : 1 ≤ 128).trans
    (hΛc.trans ((Nat.le_max_left _ _).trans hΛ))
  have hA : ∀ k, 0 ≤ ocA α q Λ k := fun k =>
    (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛ1) _).le
  have hT : ∀ k, 0 ≤ ocTauPP α q Λ k := fun k =>
    (Construction.Stream.ocTauPP_pos hΛ1).le
  have hcarrierEC : IsCarrierStart α q Λ bw CH Υ j₀ :=
    IsCarrierStart.mono hA hT (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCH) hΥ.le hcarrier
  have hcar400 : IsCarrierStart α q Λ bw 1 400 j₀ :=
    IsCarrierStart.mono hA hT (le_max_right _ _) (le_max_right _ _) zero_le_one (by norm_num)
      hcarrier
  obtain ⟨Mc, hcoeff⟩ := hcoeff j₀ hcarrierEC
  refine ⟨max Mc (plan.levelFloor R C j₀), ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hΦ hκ hterm Dm hDm P a
  obtain ⟨⟨stage, hc⟩, henc⟩ := hcoeff M ((Nat.le_max_left _ _).trans hM)
    D hDα hDq hDΛ hDζ hΦ hκ hterm Dm hDm P
  obtain ⟨Gw, rootM, rootR, relabel, he, hrootM, hrootR, hstage⟩ := henc stage hc
  let x : WeakEntryData plan C :=
    ⟨(Nat.le_max_right _ _).trans hΛ, hΛc.trans ((Nat.le_max_left _ _).trans hΛ),
      o.order_N, o.order_R, o.L_eq, (Nat.le_max_right _ _).trans hL, hSX, hSZ, j₀, hcarrier,
      hcar400,
      M, (Nat.le_max_right _ _).trans hM, D, hDα, hDq, hDΛ, hDζ, hΦ, hκ, hterm, Dm, hDm, P, a⟩
  let g : WeakEntryStages x :=
    ⟨stage, Gw, rootM, rootR, relabel, hc, he, hrootM, hrootR,
      fun law hm hr aM ha haM => hstage law hm hr a aM ha haM⟩
  obtain ⟨clock⟩ := hschedule hcommon (le_max_right Υ 400) x g
  refine ⟨stage, Gw, rootM, rootR, relabel, clock.tq (M + 1), clock.CcR, clock.W,
    hc, he, hrootM, hrootR, clock.lifts, clock.chain, ?_⟩
  intro law hm hr
  refine ⟨hstage law hm hr a _ clock.start_le clock.start_upper, ?_⟩
  intro f θ hθ
  obtain ⟨r⟩ := hreduce g clock f θ hθ
  obtain ⟨p, hp⟩ := hpair hquiet g clock law hm hr f θ hθ r
  refine ⟨clock.tq, r.Ur, r.Urw, r.Urk,
    (fun v => rerootFamily relabel (r.Ur M) v (clock.tq (M + 1))),
    rerootFamily relabel (r.Ur M), p.V, p.Uw, p.Vw, p.Uk, p.Vk,
    r.reduction, rfl, rfl, rfl, hp, ?_⟩
  exact hreadout hcompare g clock law hm hr f θ hθ r p hp

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly

/-! **The paired claim (`WeakEntryPairStatement`), from four named ingredients**.
The raw family is the reduction's level-`M` family `U^{(M)}`,
re-rooted along the encoding; its initial value is its own trace at `a_M = t_{M+1}`.
* `WeakEntryRawSolutionStatement`: the re-rooted family solves the raw (width-zero) system of the
  weak stage `Gw` from that trace, with its own gradient lift. This is structural: the encoding
  keeps fluxes, pieces, weights and actual contexts, and `D.kap M = D.κ M` at the terminal level.
* `WeakEntryRawEnergyStatement`: the strong energy of `U^{(M)}` at the capped radius
  `c_K x` is at most `C_K/3 ‖f‖₂` (from the `J_w` quiet traces and coarse energies).
* `WeakEntryPairedSolveStatement`: from any datum the paired system (`S_w = isoPairedKernel r_w`)
  has a solution, with the kernel energy bound `𝓔(V) ≤ √(2|U₀|²)` (the kernel price and the drift
  data at `c_K x`).
* `WeakEntryPairedDifferenceStatement`: moment cancellation for `U - V`.
  
Glue: the strong energy transported along the encoding is that of the level-`M` family with its
weak masses (`strongEnergy_rerootFamily`, `weakEncoding_mass`), and the trace norm of a family is
bounded by its strong energy (`ofReal_sqrt_massNormSq_le_strongEnergy`). So
`𝓔(U) + 𝓔(V) ≤ (1 + √2)𝓔(U) ≤ C_K‖f‖₂`.

The degenerate cases are included:
- `f = 0`: every bound is `0`; the raw family is `0` by the reduction's uniqueness, and the
  statements ask nothing more.
- No identities in `Gw`: both systems are uncoupled scalar equations; the difference is `0`.
- `C_K < 0`: all right-hand sides are `0` and the bounds force zero energies; the glue does not
  use the sign of `C_K`.
The premise `WeakPassageQuietTraceAt 1 400` of `WeakEntryPairStatement` is not used here: the
quiet traces enter `WeakEntryRawEnergyStatement` through its proof at the plan's constants. -/

/-! ### The named ingredients -/

/-- **The raw system of the weak stage** (structural): the re-rooted level-`M` family of the
reduction solves the width-zero system of `Gw` from its trace at `a_M = t_{M+1}`. -/
def WeakEntryRawSolutionStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
    IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ →
  ∀ r : WeakEntryReduced s θ,
    ∃ Uk : ∀ v u (_ : g.Gw.fam.Γ v u), ℝ → TorusHk (R.Kw + x.Dm - 1) (ScalarH u.1.root),
      g.Gw.IsRegSolution x.P (fun _ => isoPairedKernel 0 R.nW) (fun _ => isoPairedKernel 0 R.nW)
        A.φ₀ A.hφ₀ (x.D.κ x.M) (streamVel (x.D.Φ x.M)) R.Kw (s.tq (x.M + 1)) (x.a + A.T₀)
        (fun v => rerootFamily g.relabel (r.Ur x.M) v (s.tq (x.M + 1))) (fun _ _ => 0)
        (fun _ _ => 0) (rerootFamily g.relabel (r.Ur x.M)) (rerootFamily g.relabel (r.Urw x.M)) Uk

/-- **The raw energy** of the reduction's level-`M` family, with its weak
masses, at the capped radius `c_K x`, on `[a_M, a + T₀]`. -/
def WeakEntryRawEnergyStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
    IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ →
  ∀ r : WeakEntryReduced s θ,
    strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M)
        (fun v => weakMass x.D A.Nw A.Jw A.η₀ v.1) (s.tq (x.M + 1)) (x.a + A.T₀)
        (r.Ur x.M) (r.Urw x.M) ≤
      ENNReal.ofReal (plan.CK R C / 3 * Real.sqrt (l2NormSq f))

/-- **The paired solve**: from every datum, the paired system of `Gw`
has a solution with the kernel energy bound. -/
def WeakEntryPairedSolveStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g)
    (law : BirthLaw), law.rootMass = g.rootM → law.rootReadout = g.rootR →
  ∀ U₀ : ∀ v : CompIn g.Gw.comps, TorusHk R.Kw (ScalarH v.1.root),
    ∃ (V : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk R.Kw (ScalarH v.1.root))
      (Vw : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk (R.Kw + 1) (ScalarH v.1.root))
      (Vk : ∀ v u (_ : g.Gw.fam.Γ v u), ℝ → TorusHk (R.Kw + x.Dm - 1) (ScalarH u.1.root)),
      g.Gw.IsRegSolution x.P (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW)
        (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW) A.φ₀ A.hφ₀ (x.D.κ x.M)
        (streamVel (x.D.Φ x.M)) R.Kw (s.tq (x.M + 1)) (x.a + A.T₀) U₀ (fun _ _ => 0)
        (fun _ _ => 0) V Vw Vk ∧
      strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M) (g.Gw.mass law)
          (s.tq (x.M + 1)) (x.a + A.T₀) V Vw ≤
        ENNReal.ofReal (Real.sqrt (2 * massNormSq (x.D.termRStar (plan.radius R) x.M)
          (g.Gw.mass law) (fun v => (U₀ v).val)))

/-- **The paired difference**: moment cancellation for the raw
family minus any paired solution from the same trace. -/
def WeakEntryPairedDifferenceStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g)
    (law : BirthLaw), law.rootMass = g.rootM → law.rootReadout = g.rootR →
  ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
    IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ →
  ∀ (r : WeakEntryReduced s θ)
    (V : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk R.Kw (ScalarH v.1.root))
    (Vw : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk (R.Kw + 1) (ScalarH v.1.root))
    (Vk : ∀ v u (_ : g.Gw.fam.Γ v u), ℝ → TorusHk (R.Kw + x.Dm - 1) (ScalarH u.1.root)),
    g.Gw.IsRegSolution x.P (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW)
      (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW) A.φ₀ A.hφ₀ (x.D.κ x.M)
      (streamVel (x.D.Φ x.M)) R.Kw (s.tq (x.M + 1)) (x.a + A.T₀)
      (fun v => rerootFamily g.relabel (r.Ur x.M) v (s.tq (x.M + 1))) (fun _ _ => 0)
      (fun _ _ => 0) V Vw Vk →
    strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M) (g.Gw.mass law)
        (s.tq (x.M + 1)) (x.a + A.T₀)
        (fun v t => rerootFamily g.relabel (r.Ur x.M) v t - V v t)
        (fun v t => rerootFamily g.relabel (r.Urw x.M) v t - Vw v t) ≤
      ENNReal.ofReal (plan.CK R C * x.D.eps x.M ^ (weakChi B.α B.q A.η₀ + A.σw * R.L) *
        Real.sqrt (l2NormSq f))

/-! ### Glue -/

/-- The strong energy of a re-rooted family is that of the family, with the transported
masses. -/
theorem strongEnergy_rerootFamily {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {k : ℕ}
    {G Gw : GenStage D ScalarH Dm b j₀} (ι : CompIn G.comps ≃ CompIn Gw.comps)
    (π : CompIn Gw.comps → ℝ) (π₀ : CompIn G.comps → ℝ) (hπ : ∀ v, π (ι v) = π₀ v)
    (ρ B t₀ t₁ : ℝ) (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (ScalarH v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (ScalarH v.1.root)) :
    strongEnergy ρ B π t₀ t₁ (rerootFamily ι U) (rerootFamily ι W) =
      strongEnergy ρ B π₀ t₀ t₁ U W := by
  unfold strongEnergy rerootFamily
  congr 1
  rw [← Equiv.sum_comp ι]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hπ]
  have h := ι.symm_apply_apply v
  generalize ι.symm (ι v) = w at h ⊢
  subst h
  rfl

/-- The trace norm of a family at the start of a window is bounded by its strong energy. -/
theorem ofReal_sqrt_massNormSq_le_strongEnergy {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (ρ B : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 ≤ π v) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {K : ℕ}
    (u : ∀ v, ℝ → TorusHk K (h v)) (w : ∀ v, ℝ → TorusHk (K + 1) (h v)) :
    ENNReal.ofReal (Real.sqrt (massNormSq ρ π (fun v => (u v t₀).val))) ≤
      strongEnergy ρ B π t₀ t₁ u w := by
  have hnn : ∀ v, 0 ≤ (π v)⁻¹ * factorialNormSq ρ (u v t₀).val :=
    fun v => mul_nonneg (inv_nonneg.mpr (hπ v)) (factorialNormSq_nonneg ρ _)
  have hm : 0 ≤ massNormSq ρ π (fun v => (u v t₀).val) := Finset.sum_nonneg fun v _ => hnn v
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hm (by norm_num)]
  unfold strongEnergy
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [massNormSq, ENNReal.ofReal_sum_of_nonneg fun v _ => hnn v]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (hπ v))]
  refine mul_le_mul_right (le_trans ?_ le_self_add) _
  exact le_iSup₂_of_le (f := fun t (_ : t ∈ Set.Icc t₀ t₁) =>
    ENNReal.ofReal (factorialNormSq ρ (u v t).val)) t₀ ⟨le_rfl, ht⟩ le_rfl

/-- `(1 + √2)·(c/3)⁺ ≤ c⁺`. -/
theorem one_add_sqrt_two_mul_ofReal_third_le (c : ℝ) :
    (1 + ENNReal.ofReal (Real.sqrt 2)) * ENNReal.ofReal (c / 3) ≤ ENNReal.ofReal c := by
  have hs : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hs0,
    ← ENNReal.ofReal_mul (by linarith)]
  by_cases hc : 0 ≤ c
  · refine ENNReal.ofReal_le_ofReal ?_
    have : (1 + Real.sqrt 2) * c ≤ 3 * c := mul_le_mul_of_nonneg_right (by linarith) hc
    linarith
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))]
    exact bot_le

/-! ### The assembly -/

/-- **The paired claim from its four named ingredients.** -/
theorem weak_entry_pair_of_ingredients (plan : WeakEntryGluePlan)
    (hsol : WeakEntryRawSolutionStatement plan) (hraw : WeakEntryRawEnergyStatement plan)
    (hpaired : WeakEntryPairedSolveStatement plan)
    (hdiff : WeakEntryPairedDifferenceStatement plan) : WeakEntryPairStatement plan := by
  intro _hquiet B A R C x g s law hm hr f θ hθ r
  set aM := s.tq (x.M + 1) with haM
  set U₀ : ∀ v : CompIn g.Gw.comps, TorusHk R.Kw (ScalarH v.1.root) :=
    fun v => rerootFamily g.relabel (r.Ur x.M) v aM with hU₀
  obtain ⟨Uk, hU⟩ := hsol g s f θ hθ r
  obtain ⟨V, Vw, Vk, hV, hVe⟩ := hpaired g s law hm hr U₀
  refine ⟨⟨V, rerootFamily g.relabel (r.Urw x.M), Vw, Uk, Vk⟩, ?_⟩
  refine ⟨A.mass, hU, hV, ?_, hdiff g s law hm hr f θ hθ r V Vw Vk hV⟩
  -- the energies
  have hΛ : 1 ≤ x.D.Λ := by
    rw [x.base_eq]; exact le_trans (by norm_num) x.base128
  have hmass : ∀ v, g.Gw.mass law (g.relabel v) = weakMass x.D A.Nw A.Jw A.η₀ v.1 :=
    weakEncoding_mass A.Nw A.Jw A.η₀ g.rootM g.rootR _ _ g.relabel g.encoding law hm
  have hπ : ∀ v', 0 ≤ g.Gw.mass law v' := by
    intro v'
    obtain ⟨v, rfl⟩ := g.relabel.surjective v'
    rw [hmass v]
    exact (weakMass_pos x.D A.Nw A.Jw A.η₀ A.Nw_pos A.Jw_pos
      (fun _ => Construction.Stream.ocEpsilon_pos hΛ) v.1).le
  have haT : aM ≤ x.a + A.T₀ := s.finish.trans (by linarith [A.τ_small])
  have hEU : strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M) (g.Gw.mass law) aM
      (x.a + A.T₀) (rerootFamily g.relabel (r.Ur x.M)) (rerootFamily g.relabel (r.Urw x.M)) ≤
      ENNReal.ofReal (plan.CK R C / 3 * Real.sqrt (l2NormSq f)) := by
    rw [strongEnergy_rerootFamily g.relabel _ _ hmass]
    exact hraw g s f θ hθ r
  have hEV : strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M) (g.Gw.mass law) aM
      (x.a + A.T₀) V Vw ≤ ENNReal.ofReal (Real.sqrt 2) *
        strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M) (g.Gw.mass law) aM
          (x.a + A.T₀) (rerootFamily g.relabel (r.Ur x.M))
          (rerootFamily g.relabel (r.Urw x.M)) := by
    refine hVe.trans ?_
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    exact mul_le_mul_right (ofReal_sqrt_massNormSq_le_strongEnergy _ _ _ hπ haT _ _) _
  calc _ ≤ _ + ENNReal.ofReal (Real.sqrt 2) * _ := add_le_add le_rfl hEV
    _ = (1 + ENNReal.ofReal (Real.sqrt 2)) *
          strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M) (g.Gw.mass law) aM
            (x.a + A.T₀) (rerootFamily g.relabel (r.Ur x.M))
            (rerootFamily g.relabel (r.Urw x.M)) := by ring
    _ ≤ (1 + ENNReal.ofReal (Real.sqrt 2)) *
          ENNReal.ofReal (plan.CK R C / 3 * Real.sqrt (l2NormSq f)) := mul_le_mul_right hEU _
    _ ≤ ENNReal.ofReal (plan.CK R C * Real.sqrt (l2NormSq f)) := by
      rw [show plan.CK R C / 3 * Real.sqrt (l2NormSq f) =
        plan.CK R C * Real.sqrt (l2NormSq f) / 3 by ring]
      exact one_add_sqrt_two_mul_ofReal_third_le _

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Assembly

/-! **The weak readout (`WeakEntryReadoutStatement`), from three named ingredients**.
The readout of `Gw` is the
composed weak readout of the schedule, `Ww t z = W_M t (z ∘ ι)`
(`IsWeakReadoutChain`: `W_{M+J_w}` the root value, `W_{i-1} = W_i Λ_i 𝓡_i`).

Ingredients, at the plan:
* `WeakReadoutLinearStatement`: linearity of `Ww t` on fields of class `C^{L_w+3}`
  (`Ww t (z₁ + c • z₂) = Ww t z₁ + c • Ww t z₂`), the form of `IsWeakReadout`'s clause 2. The glued
  lifts differentiate their input (`liftApply` reads `orderedDerivative`, an iterated `fderiv`), so
  additivity holds only where the inputs are differentiable. Homogeneity on non-smooth fields is not
  asserted. No consumer needs it: `EntryTerminal.Route.readoutGlue` uses only `map_sub` at two
  classical representatives of order `≥ L_w + 3`, which are `C^{L_w+3}` by `IsClassicalRep`;
  `Ww t 0 = 0` is the case `z₁ = z₂ = 0`, `c = 1`.
* `WeakReadoutBoundStatement`: the scaled Sobolev readout bound
  `‖Ww t a_z‖_{C^s} ≤ C_read ε_{M+J_w}^{-(1+s)} |z|_{c_K x, L_w+5; π}` on classical representatives
  of the order `L_w + 3` (`z` at the order `L_w + 5`).
* `WeakReadoutIdentityStatement`: the weak identity on `[a + τ, a + T₀]`: a periodic representative
  `Θ_t` of `θ(t)` with `‖Θ_t − Ww t a_V‖_{C^s} ≤ C_id ε_M^{P_w} ‖f‖₂` (the telescoped lifted
  comparison errors plus `Ww(U − V)`).
`weak_entry_readout_parts` gives the four clauses of `IsWeakReadout`.

The degenerate cases are included:
- `f = 0`: `θ = 0` and `V = 0` (uniqueness), so `Θ_t = 0` and the identity bound is `0`.
- `z₂ = 0` in the linearity clause: `Ww t (z₁ + c • 0) = Ww t z₁`; `z₁ = z₂ = 0`, `c = 1`:
  `Ww t 0 = 0`.
- `J_w = 1`: one glued lift; the readout reads `L_w = N_w` derivatives. -/

/-- The readout of `Gw`: the composed weak readout of the schedule at the level `M`, along the
re-rooting. -/
def weakEntryReadoutMap {plan : WeakEntryGluePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    {g : WeakEntryStages x} (s : WeakEntrySchedule g) :
    ℝ → (CompIn g.Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ :=
  fun t z y => s.W x.M t (fun v y' => z (g.relabel v) y') y

/-- **Linearity of the readout on `C^{L_w+3}` fields**. -/
def WeakReadoutLinearStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g) (t : ℝ)
    (z₁ z₂ : CompIn g.Gw.comps → Vec 2 → ℝ) (c : ℝ),
    (∀ v, ContDiff ℝ ((A.Lw + 3 : ℕ) : ℕ∞) (z₁ v)) →
    (∀ v, ContDiff ℝ ((A.Lw + 3 : ℕ) : ℕ∞) (z₂ v)) →
    weakEntryReadoutMap s t (fun v => z₁ v + c • z₂ v) =
      weakEntryReadoutMap s t z₁ + c • weakEntryReadoutMap s t z₂

/-- **The scaled Sobolev readout bound**, with `z` at the order
`L_w + 5` and its classical representatives at the order `L_w + 3`. -/
def WeakReadoutBoundStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g)
    (law : BirthLaw), law.rootMass = g.rootM → law.rootReadout = g.rootR →
  ∀ (t : ℝ) (z : ∀ v : CompIn g.Gw.comps, TorusHk (A.Lw + 5) (ScalarH v.1.root))
    (az : CompIn g.Gw.comps → Vec 2 → ℝ),
    (∀ v, IsClassicalRep (z v) (az v) (A.Lw + 3)) →
    CsNormLe B.s (weakEntryReadoutMap s t az)
      (plan.Cread R C * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
        weightedNorm (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law) (fun _ => 1) z)

/-- **The weak identity** on `[a + τ, a + T₀]`. -/
def WeakReadoutIdentityStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g)
    (law : BirthLaw), law.rootMass = g.rootM → law.rootReadout = g.rootR →
  ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
    IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ →
  ∀ (r : WeakEntryReduced s θ) (p : WeakEntryPair (g := g)), WeakEntryPairBounds r law f p →
  ∀ t ∈ Set.Icc (x.a + A.τ) (x.a + A.T₀), ∀ aV : CompIn g.Gw.comps → Vec 2 → ℝ,
    (∀ v, IsClassicalRep (p.V v t) (aV v) (A.Lw + 3)) →
    ∃ Θt : Vec 2 → ℝ, IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict AVenhance.unitCube] θ t ∧
      CsNormLe B.s (fun y => Θt y - weakEntryReadoutMap s t aV y)
        (plan.Cid R C * x.D.eps x.M ^ A.Pw * Real.sqrt (l2NormSq f))

/-- **The four clauses of the readout from the three ingredients**: the four clauses of `IsWeakReadout`. -/
theorem weak_entry_readout_parts (plan : WeakEntryGluePlan)
    (hlin : WeakReadoutLinearStatement plan) (hbound : WeakReadoutBoundStatement plan)
    (hid : WeakReadoutIdentityStatement plan)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g)
    (law : BirthLaw) (hm : law.rootMass = g.rootM) (hr : law.rootReadout = g.rootR)
    (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (r : WeakEntryReduced s θ) (p : WeakEntryPair (g := g)) (hp : WeakEntryPairBounds r law f p) :
    IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ ∧
      (∀ t (z₁ z₂ : CompIn g.Gw.comps → Vec 2 → ℝ) (c : ℝ),
        (∀ v, ContDiff ℝ ((A.Lw + 3 : ℕ) : ℕ∞) (z₁ v)) →
        (∀ v, ContDiff ℝ ((A.Lw + 3 : ℕ) : ℕ∞) (z₂ v)) →
        weakEntryReadoutMap s t (fun v => z₁ v + c • z₂ v) =
          weakEntryReadoutMap s t z₁ + c • weakEntryReadoutMap s t z₂) ∧
      (∀ t (z : ∀ v : CompIn g.Gw.comps, TorusHk (A.Lw + 5) (ScalarH v.1.root))
        (az : CompIn g.Gw.comps → Vec 2 → ℝ), (∀ v, IsClassicalRep (z v) (az v) (A.Lw + 3)) →
        CsNormLe B.s (weakEntryReadoutMap s t az)
          (plan.Cread R C * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
            weightedNorm (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law) (fun _ => 1) z)) ∧
      ∀ t ∈ Set.Icc (x.a + A.τ) (x.a + A.T₀), ∀ aV : CompIn g.Gw.comps → Vec 2 → ℝ,
        (∀ v, IsClassicalRep (p.V v t) (aV v) (A.Lw + 3)) →
        ∃ Θt : Vec 2 → ℝ, IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict AVenhance.unitCube] θ t ∧
          CsNormLe B.s (fun y => Θt y - weakEntryReadoutMap s t aV y)
            (plan.Cid R C * x.D.eps x.M ^ A.Pw * Real.sqrt (l2NormSq f)) :=
  ⟨hθ, fun t z₁ z₂ c h₁ h₂ => hlin g s t z₁ z₂ c h₁ h₂,
    fun t z az haz => hbound g s law hm hr t z az haz,
    fun t ht aV haV => hid g s law hm hr f θ hθ r p hp t ht aV haV⟩

end AVRegularity.WeakEntryProofs.Assembly
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Assembly

/-! The clock, full-family lift production and finite readout composition are
separate obligations. In particular, inherited path lifts are not full-fiber lifts. -/

/-- A pinned clock before the scalar datum or any solution is chosen. -/
structure WeakPinnedClock {plan : WeakEntryGluePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} (x : WeakEntryData plan C) where
  tq : ℕ → ℝ
  start : x.a < tq (x.M + A.Jw + 1)
  finish : tq (x.M + 1) ≤ x.a + A.τ
  start_le : x.a ≤ tq (x.M + 1)
  start_upper : tq (x.M + 1) ≤ x.a + 6 * A.Jw * ocTauPP B.α B.q A.Λ (x.M + 1)
  quietMargins : ∀ i, x.M < i → i ≤ x.M + A.Jw →
    (∃ l : ℤ, tq i = ((l : ℝ) + 1 / 2) * ocTauPP x.D.α x.D.q x.D.Λ i) ∧
    tq (i + 1) + ocTauP x.D.α x.D.q x.D.Λ i ≤ tq i ∧
    tq i < tq (i + 1) + ocTauPP x.D.α x.D.q x.D.Λ i + ocTauP x.D.α x.D.q x.D.Λ i ∧
    tq i ≤ tq (i + 1) + 2 * ocTauPP x.D.α x.D.q x.D.Λ i ∧
    tq i ∈ ocQuietTimes x.D.α x.D.q x.D.Λ x.D.ζ i

/-- The common plan must put the finite wait before tau. This condition is on
its level threshold, not an extra premise on the statement. -/
def WeakScheduleWaitStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} (x : WeakEntryData plan C),
    (1 + 2 * A.Jw) * ocTauPP B.α B.q A.Λ (x.M + 1) ≤ A.τ

def WeakPinnedClockStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} (x : WeakEntryData plan C),
    Nonempty (WeakPinnedClock x)

/-- Full readout fibers at every odd native slot, at the requested two slow/fast
reserves. This is stronger than the inherited path lifts of a weak passage. -/
def WeakFullReadoutLiftsStatement (plan : WeakEntryGluePlan) : Prop :=
  WeakEntryCommonOK plan →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)}, 400 ≤ C.Υ →
    ∀ {x : WeakEntryData plan C} (g : WeakEntryStages x),
    ∃ CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (g.stage i).comps)
        (fun v => ScalarH v.1.root),
      ∀ i, x.M < i → i ≤ x.M + A.Jw →
        IsWeakReadoutLifts i A.Nw (A.Jw * A.Rw) R.sX R.sZ (g.stage i) (CcR i)

/-- Pure finite downward composition; it consumes coefficients, not their PDE. -/
def WeakReadoutChainStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (g.stage i).comps)
      (fun v => ScalarH v.1.root)),
    ∃ W, IsWeakReadoutChain x.M A.Jw A.Nw 0 A.η₀ (fun _ => A.Jw * A.Rw) g.stage CcR W

/-- The exact schedule leaf, without a datum or a new independence hypothesis. -/
theorem weak_entry_schedule_of_ingredients (plan : WeakEntryGluePlan)
    (hclock : WeakPinnedClockStatement plan) (hlifts : WeakFullReadoutLiftsStatement plan)
    (hchain : WeakReadoutChainStatement plan) : WeakEntryScheduleStatement plan := by
  intro hplan B A R C hΥ x g
  obtain ⟨clock⟩ := hclock x
  obtain ⟨CcR, hCcR⟩ := hlifts hplan hΥ g
  obtain ⟨W, hW⟩ := hchain g CcR
  exact ⟨⟨clock.tq, clock.start, clock.finish, clock.start_le, clock.start_upper,
    clock.quietMargins, CcR, hCcR, W, hW⟩⟩

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
namespace AVRegularity.WeakEntryProofs.Assembly

/-! The local coefficient hypothesis for full native readout fibers.
The lift solver and its all-order compatibility are proved. -/

/-- Local reserved models of the entire native fiber, at every admissible slow
point. Here the native chain has no bounded child carrier; all slow points are
required. This is not the independent parameter box of the producer. -/
def WeakFullReadoutModelsStatement (plan : WeakEntryGluePlan) : Prop :=
  WeakEntryCommonOK plan →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)}, 400 ≤ C.Υ →
    ∀ {x : WeakEntryData plan C} (g : WeakEntryStages x) (i : ℕ), x.M < i → i ≤ x.M + A.Jw →
    ∀ (k : ℤ) (hk : Odd k) (H : ℕ) (Y₀ : Vec 2),
    ∃ (V : Set (Vec 2))
      (edge' : ConstituentEdges x.Dm (fun _ : CompIn (g.stage i).comps => ℝ)),
      IsOpen V ∧ Y₀ ∈ V ∧
      (∀ t ∈ Set.Icc (x.D.slotStart i k / x.D.cellScaleSq i)
          ((((k : ℝ) + 61 / 48) * ocTau x.D.α x.D.q x.D.Λ i) / x.D.cellScaleSq i),
        SlowOpenEdgeEq V t (familyLiftData x.D i k (nativeChain i k) (x.D.eps (i - 1))
          ((g.stage i).fam.fiber ⟨k, hk⟩ ((g.stage i).actual ⟨k, hk⟩))).edge edge') ∧
      Nonempty (∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        JointSourceReserve H (fun t z Y => γ.coeff β t Y z))

/-- Full readout lifts from concrete local models, using the native full
lift constructor and its order-coherence theorem, not a new cell PDE argument. -/
theorem weak_full_readout_lifts_of_models (plan : WeakEntryGluePlan)
    (hmodels : WeakFullReadoutModelsStatement plan) : WeakFullReadoutLiftsStatement plan := by
  classical
  intro hplan B A R C hΥ x g
  have hΛ : 1 ≤ x.D.Λ := by
    rw [x.base_eq]
    exact (by norm_num : 1 ≤ 128).trans x.base128
  have hζ : IsFastProfile x.D.ζ := by rw [x.profile_eq]; exact B.hζ
  have hband : IsOCBandChain x.D.α x.D.q x.D.Λ x.D.ζ x.D.term x.D.κ := by
    rw [x.alpha, x.q_eq, x.base_eq, x.profile_eq, x.terminal]
    exact x.band
  have hDm : 1 ≤ x.Dm := (Nat.le_add_right 1 _).trans x.order_ge
  have one : ∀ i, x.M < i → i ≤ x.M + A.Jw →
      ∃ CcR, IsWeakReadoutLifts i A.Nw (A.Jw * A.Rw) R.sX R.sZ (g.stage i) CcR := by
    intro i hi hit
    have slot : ∀ k (hk : Odd k), ∃ Cc,
        IsLiftSequence (familyLiftData x.D i k (nativeChain i k) (x.D.eps (i - 1))
          ((g.stage i).fam.fiber ⟨k, hk⟩ ((g.stage i).actual ⟨k, hk⟩))) R.sX R.sZ
          (x.D.slotStart i k / x.D.cellScaleSq i)
          ((((k : ℝ) + 61 / 48) * ocTau x.D.α x.D.q x.D.Λ i) / x.D.cellScaleSq i)
          A.Nw (A.Jw * A.Rw) Cc := by
      intro k hk
      have hc := native_full_lift_all_orders x.D hζ hΛ i
        (weakData_kap_pos x.D hΛ hζ hband i) k hk (nativeChain i k)
        (by simp [nativeChain]) (x.D.eps (i - 1))
        ((g.stage i).fam.fiber ⟨k, hk⟩ ((g.stage i).actual ⟨k, hk⟩)) _ _
        (weakData_lift_window_strict x.D hΛ hζ hband i k)
        A.Nw (A.Jw * A.Rw) hDm Set.univ isOpen_univ
        (fun H Y₀ _ => hmodels hplan hΥ g i hi hit k hk H Y₀) R.sX R.sZ
      exact ⟨_, liftSequence_of_on_univ _ _ _ _ _ _ _ _ hc⟩
    refine ⟨fun k => if hk : Odd k then Classical.choose (slot k hk) else 0, ?_⟩
    intro k hk
    simp only [dite_eq_left hk]
    exact Classical.choose_spec (slot k hk)
  refine ⟨fun i => if hi : x.M < i ∧ i ≤ x.M + A.Jw then
      Classical.choose (one i hi.1 hi.2) else 0, ?_⟩
  intro i hi hit
  simp only [dite_eq_left (And.intro hi hit)]
  exact Classical.choose_spec (one i hi hit)

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Providers.QuietAtlas
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Parent jets are needed only on the backward middle half of the pinned slow
quiet margin. History quietness includes every active child's entire availability hull. -/

/-- Only this middle-half interval is used for parent coefficient jets. -/
def weakMiddleHalf {plan : WeakPassagePlan} {B} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) : Set ℝ :=
  Set.Icc (r.tq i - ocTauP c.D.α c.D.q c.D.Λ i / 2) (r.tq i)

/-- Pure common-plan scale conditions. The auxiliary carrier start is used only
for availability geometry and does not change the stage's own carrier. -/
def WeakQuietGeometryPlanOK (plan : WeakPassagePlan) : Prop :=
  ∀ {B} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R),
    (∃ j : ℕ, j ≤ c.M + 1 ∧ IsCarrierStart B.α B.q A.Λ 1 1 1 j) ∧
    ∀ i, c.M < i → i ≤ c.M + A.Jw →
      c.D.eps (i - 1) ^ 2 / c.D.κ c.M ≤ ocTauP c.D.α c.D.q c.D.Λ i / 2

/-- Parent-scale Schur jets, stated on the entire backward middle half so the
heat-window restriction is an independent, routine operation. -/
def WeakMiddleHalfJets {plan : WeakPassagePlan} {B} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) : Prop :=
  ∃ b : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ,
    (∀ v u, 0 ≤ b v u) ∧ (∀ v, ∑ u, b v u ≤ plan.coeffC R) ∧
    (∀ u, ∑ v, b v u ≤ plan.coeffC R) ∧
    (∀ v u (γ : (c.stage i).fam.Γ v u) d, 2 ≤ d → d ≤ c.Dm →
      ∀ t ∈ Set.Icc (r.tq i - ocTauP c.D.α c.D.q c.D.Λ i / 2) (r.tq i),
        ContDiff ℝ (plan.jetOrder R) ((c.stage i).physCoeff v u γ d t)) ∧
    ∀ v u,
      ENNReal.ofReal (Real.sqrt (weakMass c.D A.Nw A.Jw A.η₀ u.1 /
        weakMass c.D A.Nw A.Jw A.η₀ v.1)) *
      ∑ γ : (c.stage i).fam.Γ v u, ∑ d ∈ Finset.Icc 2 c.Dm,
        coefficientSeminorm (c.D.eps (i - 1)) (plan.jetOrder R)
          (r.tq i - ocTauP c.D.α c.D.q c.D.Λ i / 2) (r.tq i)
          ((c.stage i).physCoeff v u γ d) *
          (ENNReal.ofReal (c.D.κ c.M * c.D.eps (i - 1) ^ (d - 2)))⁻¹ ≤ ENNReal.ofReal (b v u)

/-- Exact hard analytic leaf: Cauchy/Piola parent jets after the whole finer
history is quiet. No independence or coefficient estimate is claimed off this set. -/
def WeakMiddleHalfJetsStatement (plan : WeakPassagePlan) : Prop :=
  WeakPassageCommonOK plan →
  ∀ {B} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → WeakQuietWindow c r i →
    IsHistoryQuiet c.D (c.M + A.Jw) i (weakMiddleHalf c r i) → WeakMiddleHalfJets c r i

/-- Pure quiet margin/history geometry, with the scale hypotheses stated separately. -/
def WeakMiddleHalfHistoryStatement (plan : WeakPassagePlan) : Prop :=
  WeakQuietGeometryPlanOK plan →
  ∀ {B} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → WeakQuietWindow c r i →
    IsHistoryQuiet c.D (c.M + A.Jw) i (weakMiddleHalf c r i)

/-- Exact coefficient layer: the heat interval fits inside the history-quiet middle half, then
coefficient seminorms decrease when restricted to that interval. -/
theorem weak_quiet_coefficient_of_ingredients (plan : WeakPassagePlan)
    (hplan : WeakQuietGeometryPlanOK plan) (hcommon : WeakPassageCommonOK plan)
    (hhistory : WeakMiddleHalfHistoryStatement plan)
    (hjets : WeakMiddleHalfJetsStatement plan) : WeakQuietCoefficientStatement plan := by
  intro B A R c r i hi hit hw
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge)
  have he : 0 < c.D.eps (i - 1) := Construction.Stream.ocEpsilon_pos hΛ
  have hκ : 0 < c.D.κ c.M := by
    have h := CycleReference.bandChain_pos ((by norm_num : 1 ≤ 128).trans
      ((plan.base_ge B).trans c.base_ge)) B.hζ c.band (le_refl c.M)
    exact h
  have hfit := (hplan c).2 i hi hit
  have hP := Velocity.Jets.ocTauP_pos (α := c.D.α) (q := c.D.q) (m := i) hΛ
  have hleft : r.tq (i + 1) ≤ r.tq i - ocTauP c.D.α c.D.q c.D.Λ i / 2 :=
    (hw.2.2.2.2 ⟨le_rfl, sub_le_self _ (by positivity)⟩).1
  have hheat : Set.Icc (r.tq i - c.D.eps (i - 1) ^ 2 / c.D.κ c.M) (r.tq i) ⊆
      weakMiddleHalf c r i := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨b, hb, hr, hc, hsmooth, hnorm⟩ := hjets hcommon c r i hi hit hw (hhistory hplan c r i hi hit hw)
  refine ⟨he, hκ, ?_, ?_, b, hb, hr, hc, ?_, ?_⟩
  · linarith only [hleft, hfit]
  · linarith only [hfit]
  · intro v u γ d hd hdD t ht
    exact hsmooth v u γ d hd hdD t (hheat ht)
  · intro v u
    apply le_trans _ (hnorm v u)
    apply mul_le_mul' le_rfl
    apply Finset.sum_le_sum
    intro γ _
    apply Finset.sum_le_sum
    intro d _
    apply mul_le_mul' _ le_rfl
    exact CycleJointProofs.coefficientSeminorm_time_mono _ _ _ _ _ _ hheat _

end AVRegularity.WeakEntryProofs.Assembly
end
end
end
