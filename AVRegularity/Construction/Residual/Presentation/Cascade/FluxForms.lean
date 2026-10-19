-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.NativeLiftedFieldCovarianceEnergy
public import AVRegularity.Construction.Residual.Presentation.PlainToKernel
import AVRegularity.Construction.Residual.Presentation.Cascade.CtxFloors
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
public import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerStatements
public import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleResidualDifferentiated
import AVRegularity.Proofs.Results.Construction.SuccessorFluxUnique

section
section
/-! **Promotion of a lift sequence to the orders of a setting, with no bound on its own orders**
(cascade side of the bill residual).

`liftSequence_promote_of_setting`: under a lift setting at the orders `(K, k, L)`, a lift sequence
of ANY stored orders `(s_X, s_Z)` for the same operator data is a lift sequence at the orders
`(K + D + 2, max (k + 1) (L + 2))` of the existence theorem. It is
`positive_layer_lift_sequence_promote` without its hypotheses `s_X ≤ q_s`, `s_Z ≤ q_f`: the
uniqueness is applied at the minimum of the two pairs of orders, and that minimum is below the
stored orders of the setting through the second member (`K + D + 2 ≤ q_s`,
`max (k + 1) (L + 2) ≤ q_f`, by the two equations `qs_eq`, `qf_eq` of `IsLiftSetting`).

The cascade needs this form: in the passage statements the lift orders `s_X`, `s_Z` of the given
lifted field are universally quantified above a floor, so no stored order of a setting bounds
them, while the stored orders of a setting are fixed by its orders.

For `s_X = s_Z = 0` the given sequence has no regularity clause to compare and the minimum is
`0`; for `s_X`, `s_Z` above the orders of the window the conclusion is also the monotonicity
`isLiftSequence_mono`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.Construction.Residual.Presentation.Cascade

open CycleComparison.Reconstruction CycleComparison.Lift

variable {ι : Type} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bb : ι → ι → ℝ} {Θ : ℝ}

/-- **A lift sequence of any stored orders is a lift sequence at the orders of the setting.** -/
theorem liftSequence_promote_of_setting
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bb Θ)
    {sX sZ : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h} (hC : IsLiftSequence Q sX sZ a b N H Cc) :
    IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc := by
  have hD := P.D_ge
  have hqs : K + D + 2 ≤ qs := by
    rw [P.qs_eq]
    have h1 : N + D ≤ (N + D) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h2 : (N + D) ^ 2 ≤ (H + 1) * (N + D) ^ 2 := Nat.le_mul_of_pos_left _ (Nat.succ_pos H)
    have h3 : 4 * ((H + 1) * (N + D) ^ 2) = 4 * (H + 1) * (N + D) ^ 2 := by ring
    omega
  have hqf : max (k + 1) (L + 2) ≤ qf := by
    rw [P.qf_eq]
    have h1 : max (k + 1) (L + 2) ≤ max k (L + 2) + 1 := by
      rcases le_total k (L + 2) with hk | hk
      · rw [max_eq_right hk]; exact max_le (by omega) (by omega)
      · rw [max_eq_left hk]; exact max_le (by omega) (by omega)
    omega
  obtain ⟨Cc', hC'⟩ := Providers.cycle_lift_exists N K k L D H CG Cw Cj Q π a b
    e ν B ρ E ℓ dstar εc lam par V qs qf bb Θ P
  have he := Providers.lift_sequence_unique Q π a b e ν B ρ E ℓ dstar εc lam par V
    H N K k L qs qf CG Cw Cj bb Θ P
    (min sX (K + D + 2)) (min sZ (max (k + 1) (L + 2)))
    ((min_le_right _ _).trans hqs) ((min_le_right _ _).trans hqf) Cc Cc'
    (isLiftSequence_mono hC (min_le_left _ _) (min_le_left _ _))
    (isLiftSequence_mono hC' (min_le_right _ _) (min_le_right _ _))
  refine ⟨hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1, ?_, ?_⟩
  · intro hh hhH n m α v u t ht
    have hf : (fun X z => Cc hh n m α t X z v u) =
        (fun X z => Cc' hh n m α t X z v u) :=
      funext fun X => funext fun z => he hh hhH n m α t ht X z v u
    refine ⟨?_, (hC.2.2.2.2.2.1 hh hhH n m α v u t ht).2⟩
    rw [hf]
    exact (hC'.2.2.2.2.2.1 hh hhH n m α v u t ht).1
  · intro hh hhH n hn hnN f hf X
    refine ⟨?_, (hC.2.2.2.2.2.2 hh hhH n hn hnN f hf X).2⟩
    intro t ht
    have ha := liftApply_congr_at_time n (Cc hh n) (Cc' hh n) (fun _ => f) t
      (fun m α Y z v u => he hh hhH n m α t ht Y z v u)
    change ContDiff ℝ (max (k + 1) (L + 2) : ℕ∞) (liftApply n (Cc hh n) (fun _ => f) t X)
    rw [ha]
    exact (hC'.2.2.2.2.2.2 hh hhH n hn hnN f hf X).1 t ht

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The native lift setting of an odd slot of a cascade stage, at the full effective order**
(cascade side of the bill residual).

`uniform_native_slot_lifts` hides the effective order `cap ≤ D_m` of its slot lifts. The
window of the reconstruction needs the setting of `restrictLiftData D_m le_rfl …`, whose stored
orders are `q_s = K + 4(H+1)(N+D_m)^2`, `q_f = max k (L+2) + H D_m + 2N + 2 D_m` (fields `qs_eq`,
`qf_eq` of `IsLiftSetting`: they are not free). This module repeats the first half of that proof
with `K_src = D_m`, and keeps the setting.

For an empty family `windowEdges` is the empty list. -/

@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Construction.Residual.Presentation.Cascade
open AVRegularity.Construction.Preservation AVRegularity.Construction.Preservation.FullLift
open AVRegularity.EntryWeakProofs

/-- **The native lift setting of the odd slot `slot` of the stage `G`** at the slow length
`liftLength D G.level`, restricted at the full order `D_m`, on the native window of the slot. -/
def NativeStageSetting {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData}
    {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (G : GenStage D hr Dm bw j₀) (law : BirthLaw) (m : ℕ)
    (H N K k L : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (S : ℝ) (slot : OddSlot) : Prop :=
  let a := D.slotStart m slot.1 / D.cellScaleSq m
  let b := (((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m
  let Q := familyLiftData D m slot.1 (nativeChain m slot.1) (liftLength D m)
    (G.fam.fiber slot (G.actual slot))
  IsLiftSetting (restrictLiftData Dm le_rfl {Q with edge := windowEdges a b Q.edge})
    (G.mass law) a b (D.eps m) (D.kap m) (D.kap (m - 1))
    (liftLength D m)
    (D.eps (m - 1)) (D.eps m / Real.sqrt (D.kap m))
    (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)))
    (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / liftLength D m)
    (liftLength D m / D.eps (m - 1)) (pulseParallel slot.1)
    (pulseShearProfile D.α D.q D.Λ m D.ζ (D.kap m) slot.1)
    H N K k L (K + 4 * (H + 1) * (N + Dm) ^ 2)
    (max k (L + 2) + H * Dm + 2 * N + 2 * Dm) CG Cw Cj (recordMajorant (G.mass law) G.fam) S

/-- The native setting of the odd slots of a stage of the cascade invariant at level
`m₀ ≤ G.level < D.term`, at `ρ = liftLength D G.level`, restricted at the full order `D_m`, with
constants chosen before the stage. -/
theorem native_stage_setting {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ bw : ℝ, 0 < bw →
    ∀ Dm H N K k L : ℕ, 2 ≤ Dm → 1 ≤ N →
    ∃ (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (m₀ : ℕ), 2 ≤ m₀ ∧ (∀ r q, 0 ≤ Cj r q) ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (j₀ : ℕ) (G : GenStage D hr Dm bw j₀) (law : BirthLaw) (P : ProvParams)
      (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
      (M : ℕ) (kI : InvConsts) (tA tB S θK : ℝ),
    IsStageInvariant law P seedK freshK φ₀ hφ₀ M kI tA tB S θK G →
    m₀ ≤ G.level → G.level < D.term → j₀ ≤ G.level → G.fam.HasDepthAtMost H →
    (∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1) →
    (∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2) →
    (∀ v u γ, 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level) →
    ∀ slot : OddSlot, ∀ m : ℕ, G.level = m →
      NativeStageSetting G law m H N K k L CG Cw Cj S slot := by
  classical
  obtain ⟨Λa, hΛa, ha⟩ := uniform_native_lift_analytic_certificates hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Λs, hΛs, hs⟩ := native_lift_scale_bounds hα0 hα1 hs0 hs1 hq hζ
  refine ⟨max Λa Λs, by omega, ?_⟩
  intro Λ hΛ bw hb Dm H N K k L hDm hN
  let qs := K + 4 * (H + 1) * (N + Dm) ^ 2
  let qf := max k (L + 2) + H * Dm + 2 * N + 2 * Dm
  obtain ⟨CG, Cw, _hCG, _hCw, ma, hma, hanalytic⟩ := ha Λ (by omega) qs
  obtain ⟨ms, hms, hscale⟩ := hs Λ (by omega)
  obtain ⟨B, hB, hsource⟩ := stage_native_lift_source_exists_envelope bw hb qs qf
  let Cj : ℕ → ℕ → ℝ := fun r q => (Fintype.card (Finset.Icc 2 Dm) : ℝ) * B (r + q)
  refine ⟨CG, Cw, Cj, max ma ms, by omega,
    fun r q => mul_nonneg (Nat.cast_nonneg _) (hB _), ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq hband j₀ G law P seedK freshK φ₀ hφ₀
    M kI tA tB S θK hG hm hmM hj hdepth hreserve hreserve2 hlength slot m₁ hm₁
  subst hm₁
  have hΛ128 : 128 ≤ D.Λ := by rw [hDΛ]; omega
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hi : 1 ≤ G.level := by omega
  have hE : 0 < D.eps (G.level - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have ⟨hnat, _, _, _, hpar, hcert, _, _⟩ := hG
  have ⟨hρ, hcell, hlam⟩ := hscale D hDα hDq hDΛ hDζ hband G.level (by omega) (by omega)
  let ρ := liftLength D G.level
  let a := D.slotStart G.level slot.1 / D.cellScaleSq G.level
  let b := (((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let Q := familyLiftData D G.level slot.1 (nativeChain G.level slot.1) ρ
    (G.fam.fiber slot (G.actual slot))
  have hA := hanalytic (CompIn G.comps) (fun v => hr v.1.root) Dm D
    hDα hDq hDΛ hDζ hseq hband G.level (by omega) hmM slot.1 slot.2 ρ hρ.le
    (G.fam.fiber slot (G.actual slot))
  have hKD : Dm ≤ Dm := le_rfl
  have hz' : ∀ v u d, Dm < d.1 → Q.edge v u d = [] := by
    intro v u d hd
    exact False.elim (Nat.not_lt_of_ge (Finset.mem_Icc.mp d.2).2 hd)
  have hres := effective_lift_reserves_le K k L H N Dm Dm hKD
  have hsource' := hsource hr D Dm j₀ G law P seedK freshK φ₀ hφ₀ M kI tA tB S θK
    hG hi hj hE hqD hΛ128 hζD hband hreserve hreserve2 hlength slot
    (ρ / D.eps (G.level - 1)) (div_nonneg hρ.le hE.le) (fun _ => 1) (Or.inl rfl)
  have hsourceQ : IsScaledJetEnvelope (G.mass law) Q.edge (Set.Icc a b)
      (ρ / D.eps (G.level - 1)) Cj qs qf (recordMajorant (G.mass law) G.fam) S := by
    simpa only [Q, familyLiftData, a, b, Cj, one_pow, div_one] using hsource'
  exact native_lift_setting_of_certificates G kI M hcert hpar hnat hi hj hb
    hΛ1 hζD hband hreserve hreserve2 slot ρ hρ hcell hlam (G.mass law)
    (fun v => Buffer.birth_compMass_pos hqD hΛ128 law v.1) H N K k L Dm hN hDm hKD
    CG Cw Cj (recordMajorant (G.mass law) G.fam) S hdepth hz' hA.2.1
    (fun r hr => hA.1 r (hr.trans hres.1)) (fun r _ => hA.2.2 r)
    (scaledEnvelope_order_mono hres.1 hres.2 hsourceQ)

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
section
/-! **The reconstruction on a degenerate window** (cascade side of the bill residual).

A context of the bill has `s₀ ≤ t_p ≤ s₀ + 4τ''_m ≤ t_f`, so `t_p = t_f` is allowed, and the
comparison clauses are asserted there. The assembly `frameReconAt_of_steps` asks
`0 < t_f − t_p`. On a point the statement is elementary:

* `reconBound_degenerate`: for a frame with `F.tf = F.tp`, descending slots `K` and a
  realization `U₀` of the lifted field at the single time `t_p` at those slots,
  `ReconBound … t_p t_f ρ X` for every radius `ρ` and every `X ≥ 0`. The trajectory is constant
  equal to `U₀`, the gradient carrier and the residual pair are `0`.
* `frameReconAt_degenerate`: hence `FrameReconAt` whenever the bound `C·𝔅·A_in` is
  nonnegative.

On `[t_p, t_p]` every clause of `IsCoupledWeakSolutionTorus` is vacuous or trivial: continuity
on a point; the two clauses on the gradient carrier are asked for almost every time (the
restricted measure is `0`); the initial value is the constant; the weak identity at `t = t_p` is
`∫u₀φ − ∫fφ = ∫_{(t_p,t_p]} …` with `u₀ = f` and an empty time integral, and its two
integrability clauses in space are pairings of `L²` jets.

For an empty component family there is nothing to prove, and for `X = 0` every term vanishes. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The restriction of Lebesgue measure to a degenerate interval is zero. -/
theorem restrict_Icc_self (t : ℝ) : (volume.restrict (Set.Icc t t) : Measure ℝ) = 0 := by
  rw [Set.Icc_self]
  exact Measure.restrict_eq_zero.2 Real.volume_singleton

theorem memLp_Icc_self {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (t : ℝ) :
    MemLp f 2 (volume.restrict (Set.Icc t t)) := by
  rw [restrict_Icc_self]
  exact memLp_measure_zero

theorem integrable_Icc_self {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (t : ℝ) :
    Integrable f (volume.restrict (Set.Icc t t)) := by
  rw [restrict_Icc_self]
  exact integrable_zero_measure

theorem ae_Icc_self (P : ℝ → Prop) (t : ℝ) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc t t)), P s := by
  rw [restrict_Icc_self, ae_zero]
  exact Filter.eventually_bot

theorem integral_Icc_self (f : ℝ → ℝ) (t : ℝ) : ∫ s in Set.Icc t t, f s = 0 := by
  rw [restrict_Icc_self, integral_zero_measure]

section Point

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The weak identity of a constant trajectory at the initial time: both sides vanish. -/
theorem coupledWeakIdentity_point {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure (Vec 2)} (ν t : ℝ) (v : ℝ → Vec 2 → Vec 2) (f φ : Vec 2 → H)
    (dφ : Fin 2 → Vec 2 → H) (du : ℝ → Fin 2 → Vec 2 → H)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H)
    (hf : Integrable (fun x => inner ℝ (f x) (φ x)) μ) :
    CoupledWeakIdentity μ ν t t v f f φ dφ du flux F g := by
  dsimp only [CoupledWeakIdentity]
  refine ⟨hf, hf, fun s hs => ?_, ?_, ?_⟩
  · rw [Set.Ioc_self] at hs
    exact absurd hs (Set.notMem_empty s)
  · rw [Set.Ioc_self]
    exact integrableOn_empty
  · rw [sub_self, Set.Ioc_self, Measure.restrict_empty, integral_zero_measure]

/-- **A constant trajectory is a coupled weak solution on a degenerate interval**, for any
gradient carrier and any forcing. -/
theorem coupledWeakSolutionTorus_point (ν t : ℝ) (v : ℝ → Vec 2 → Vec 2) (D : ℕ)
    (K : ι → ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (f : ∀ i, TorusHk (K i) (h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)) :
    IsCoupledWeakSolutionTorus ν t t v D K A f F g (fun i _ => f i) w := by
  refine ⟨fun i => continuousOn_const, fun i => memLp_Icc_self _ _,
    fun i => ae_Icc_self _ _, fun i => rfl, ?_⟩
  intro i s hs φ
  have hst : s = t := le_antisymm hs.2 hs.1
  rw [hst]
  exact coupledWeakIdentity_point ν t v _ _ _ _ _ _ _
    (torusJet_inner_integrable _ _ _ _)

end Point

/-- **The reconstruction bound on a degenerate window.** -/
theorem reconBound_degenerate (F : Frame D hr Dm b j₀) (law : BirthLaw)
    (htt : F.tf = F.tp) (K : CompIn F.G.comps → ℕ) (hdesc : F.G.fam.IsDescending K)
    (U₀ : ∀ v : CompIn F.G.comps, TorusHk (K v) (hr v.1.root))
    (hU : ∀ v, (U₀ v).toFunction.jet (valueIndex2 (K v)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep F.tp x v)
    (ρ X : ℝ) (hX : 0 ≤ X) :
    ReconBound F.Mn F.G F.m F.N F.depth 0 F.CcT F.aRep (F.G.mass law) F.tp F.tf ρ X := by
  rw [htt]
  refine ⟨K, fun _ => Nat.zero_le _, fun v _ => U₀ v, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
    ?_⟩
  refine { desc := hdesc, value := ?_, plain := ?_, flux := ?_, scalar := ?_ }
  · intro t ht v
    have htp : t = F.tp := le_antisymm ht.2 ht.1
    rw [htp]
    exact hU v
  · exact coupledWeakSolutionTorus_point _ _ _ _ _ _ _ _ _ _
  · refine ⟨fun v => memLp_Icc_self _ _, ?_⟩
    rw [integral_Icc_self, mul_zero, Real.sqrt_zero]
    exact hX
  · refine ⟨fun v => integrable_Icc_self _ _, ?_⟩
    rw [integral_Icc_self]
    exact hX

/-- **The reconstruction bound at a frame with a degenerate window.** -/
theorem frameReconAt_degenerate (F : Frame D hr Dm b j₀) (law : BirthLaw)
    (htt : F.tf = F.tp) (K : CompIn F.G.comps → ℕ) (hdesc : F.G.fam.IsDescending K)
    (U₀ : ∀ v : CompIn F.G.comps, TorusHk (K v) (hr v.1.root))
    (hU : ∀ v, (U₀ v).toFunction.jet (valueIndex2 (K v)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep F.tp x v)
    (kc : ℕ) (c₀ cr c σ₀ : ℝ) (Lc Acl : ℕ) (θ₁ θ₂ Ain Cfl C : ℝ)
    (hX : 0 ≤ C * succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂ *
      Ain) :
    FrameReconAt F law kc c₀ cr c σ₀ Lc Acl θ₁ θ₂ Ain Cfl C :=
  fun _ _ _ => reconBound_degenerate F law htt K hdesc U₀ hU _ _ hX

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The retained solution at the order `N_aux + 3` and the classical representatives of the
readout and of the retained solution, at explicit data.**

From the higher retained values of the retained solution `Y` (the conclusion
`RetainedHigherValuesStatement`, a conjunct of the proved retained production bundle
`retained_production_bundle_of_certificates`, whose reserve `N_aux + 3 + 2p + 2 ≤ N_out` is
`successor_lift_gradient_trace_reserve`), the two `IsClassicalRep ... N_aux` clauses of `Frame`
hold, with the same `Yhi`. `H^{N_aux+3} ⊂ C^{N_aux+1}` is `hilbert_classicalRep_exists` at
`K = N_aux + 3`, `r = N_aux`. No time regularity of the representatives is asked.

The degenerate cases are included: an empty family (the clauses are vacuous); `tf < tp` or
`tp = tf`; `Ain = 0` (the data do not mention `Ain`). -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Residual.Presentation.Cascade
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Assembly

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The classical representatives of the retained solution and of its readout. -/
def FrameRepsClauses (G Gr : GenStage D hr Dm bw j₀) (m Naux : ℕ) (η₀ tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root)) : Prop :=
  ∃ (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root),
    (∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep
      (succReadout m (D.eps (m - 1)) η₀ Naux (fun v' => Y v' t) v) (fun x => aZ t x v) Naux) ∧
    (∀ v', ∀ t ∈ Set.Icc tp tf, IsClassicalRep (Y v' t) (fun x => aY t x v') Naux)

/-- The retained solution at the order `Naux + 3`, with `Y` its truncation on the window,
and the classical representatives at the order `Naux`. -/
theorem retained_high_and_reps (G Gr : GenStage D hr Dm bw j₀) (m Naux : ℕ)
    (η₀ tp tf : ℝ) (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (hhigher : RetainedHigherValuesStatement Gr Naux tp tf Y) :
    ∃ Yhi : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 3) (hr v.1.root),
      (∀ v, ∀ t ∈ Set.Icc tp tf,
        Y v t = truncateTorusHk (by omega : Naux ≤ Naux + 3) (Yhi v t)) ∧
      FrameRepsClauses G Gr m Naux η₀ tp tf Y := by
  classical
  obtain ⟨Yhi, heq⟩ := hhigher
  refine ⟨Yhi, heq, ?_⟩
  have hY (v' : CompIn Gr.comps) (t : ℝ) :
      ∃ a : Vec 2 → hr v'.1.root, IsClassicalRep (Yhi v' t) a Naux :=
    hilbert_classicalRep_exists (Naux + 3) Naux (by omega) (Yhi v' t)
  have hZ (v : CompIn G.comps) (t : ℝ) :
      ∃ a : Vec 2 → hr v.1.root, IsClassicalRep
        (succReadout m (D.eps (m - 1)) η₀ (Naux + 3) (fun v' => Yhi v' t) v) a Naux :=
    hilbert_classicalRep_exists (Naux + 3) Naux (by omega) _
  choose aY haY using hY
  choose aZ haZ using hZ
  refine ⟨fun t x v => aZ v t x, fun t x v' => aY v' t x, ?_, ?_⟩
  · intro v t ht
    have h := classicalRep_truncate (by omega : Naux ≤ Naux + 3) le_rfl _ _ (haZ v t)
    rw [truncate_succReadout] at h
    have he : (fun c => truncateTorusHk (by omega : Naux ≤ Naux + 3) (Yhi c t)) =
        fun c => Y c t := by
      funext c
      exact (heq c t ht).symm
    rw [he] at h
    exact h
  · intro v' t ht
    have h := classicalRep_truncate (by omega : Naux ≤ Naux + 3) le_rfl _ _ (haY v' t)
    rw [← heq v' t ht] at h
    exact h

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The lift step of the fine tail, first step: the frame's own lifted field at the order
`K + 1`.**

At explicit data (the lift coefficients `CcT`, the prepared image `PZ` with its classical
representative `aRep` of order `N_aux - 2p`, all as at a frame) the lifted field of order `K + 1`
and its gradient representative of order `K + 2` exist for the SAME `CcT, PZ, aRep`, with the
classical representatives of the glued lift. The classical order of `aRep` is one short of
`K + 2 + N`; the missing order comes from the retained solution at the order `N_aux + 3`
(`higher_readout_covariance_input_exists`), and two classical representatives of the same
`P_pZ(t)` agree (`classical_covImage_rep_unique`). The frame's `CcT` equals the native
coefficients of the slot lifts on every pulse window
(`nativeStageLiftFamily_coefficients_unique`, at any stored orders), so the glued lifts agree. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {π : CompIn G.comps → ℝ} {H N Kp kp Lp : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

/-- The prepared classical representative of a frame is `C^{K+2+N}` on the window. -/
theorem aRep_contDiff_high {Gr : GenStage D hr Dm bw j₀} (p Naux K : ℕ)
    (hk : K + 1 + N + 2 * p ≤ Naux) (η tp tf : ℝ) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (hhigh : AVRegularity.Construction.Preservation.Assembly.RetainedHigherValuesStatement
      Gr Naux tp tf Y)
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hprep : ∀ v, ∀ t ∈ Set.Icc tp tf,
      IsCovImage (covPolyP (covPrimitive D G.level t) p)
        (succReadout G.level (D.eps (G.level - 1)) η Naux (fun v' => Y v' t) v) (PZ v t) ∧
      IsClassicalRep (PZ v t) (fun x => a t x v) (Naux - 2 * p)) :
    ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((K + 2 + N : ℕ) : ℕ∞) (a t) := by
  classical
  obtain ⟨Yhi, heq⟩ := hhigh
  obtain ⟨PZ', a', hprep', hreg'⟩ := higher_readout_covariance_input_exists (S := G.comps)
    D G.level p Naux (Naux + 3) (K + 1 + N + 1) (by omega)
    (liftedField_higher_regularity_reserve (k := K + 1) (N := N) (p := p) (Naux := Naux)
      (by omega) |>.trans' (by omega))
    η tp tf hΛ hζ Y Yhi heq
  intro t ht
  refine contDiff_pi.mpr fun v => ?_
  have hu : (fun x => a t x v) = fun x => a' t x v :=
    classical_covImage_rep_unique (covPolyP (covPrimitive D G.level t) p) _ _ _
      (hprep v t ht).1 (hprep' v t ht).1 _ _ (hprep v t ht).2 (hprep' v t ht).2
  rw [hu]
  have h := contDiff_pi.mp (hreg' t) v
  have he : K + 2 + N = K + 1 + N + 1 := by omega
  rw [he]
  exact h


/-- The glued Eulerian lift of the prepared field `a` with the lift coefficients `Cc`. -/
def Glued (G : GenStage D hr Dm bw j₀) (N H : ℕ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) :
    Vec 2 → ∀ v : CompIn G.comps, hr v.1.root :=
  gluedLift (ocObsPulses D.α D.q D.Λ G.level t t)
    (fun j => ocCutoff D.α D.q D.Λ G.level j) (D.cellScaleSq G.level) (liftLength D G.level)
    (D.eps G.level) (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level) N H Cc
    (fun j s y => D.flowOf (G.level - 1) s y (D.slotAnchor G.level j))
    (fun j s y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s) a t

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The glued lift with the frame's coefficients is the glued lift with the native ones. -/
theorem Glued_eq_native
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N Kp kp Lp CG Cw Cj S)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (sX sZ : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hseq : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D G.level k (nativeChain G.level k) (liftLength D G.level)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) sX sZ
        (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        N H (CcT k))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) :
    Glued G N H CcT a t = Glued G N H (nativeStageLiftFamily slotLifts) a t := by
  classical
  funext x
  have hc : 0 < D.cellScaleSq G.level :=
    EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hband G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  apply gluedLift_coeff_congr
  intro j hj hcut hh hhh n _hn m α X z v' u
  have hjodd : Odd j := (Finset.mem_filter.mp hj).2.1
  have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
  have htcell : (D.cellScaleSq G.level)⁻¹ * t ∈
      Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) := by
    rw [inv_mul_eq_div]
    exact ⟨div_le_div_of_nonneg_right htw.1 hc.le, div_le_div_of_nonneg_right htw.2 hc.le⟩
  exact nativeStageLiftFamily_coefficients_unique slotLifts sX sZ CcT hseq
    j hjodd hh hhh n m α _ htcell X z v' u


/-- **The frame's own lifted field at the order `K + 1`**, with the frame's `CcT, PZ, aRep`. -/
theorem lift_at_order {Gr : GenStage D hr Dm bw j₀}
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N Kp kp Lp CG Cw Cj S)
    (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (m : ℕ) (hm : G.level = m) (K : ℕ) (hres : ∀ slot : OddSlot, K + 2 + (N + (slotLifts slot).cap) ≤
      Kp + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hrQ : K + 2 ≤ max kp (Lp + 2))
    (p Naux sX sZ : ℕ) (hk : K + 1 + N + 2 * p ≤ Naux) (η tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (hhigh : AVRegularity.Construction.Preservation.Assembly.RetainedHigherValuesStatement
      Gr Naux tp tf Y)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hseq : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) sX sZ
        (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)
        N H (CcT k))
    (hprep : ∀ v, ∀ t ∈ Set.Icc tp tf,
      IsCovImage (covPolyP (covPrimitive D m t) p)
        (succReadout m (D.eps (m - 1)) η Naux (fun v' => Y v' t) v) (PZ v t) ∧
      IsClassicalRep (PZ v t) (fun x => aRep t x v) (Naux - 2 * p)) :
    ∃ (u : ∀ v : CompIn G.comps, ℝ → TorusHk (K + 1) (hr v.1.root))
      (w : ∀ v : CompIn G.comps, ℝ → TorusHk (K + 1 + 1) (hr v.1.root)),
      IsLiftedFieldW G Gr m p Naux N H sX sZ η tp tf Y CcT PZ aRep u w ∧
      (∀ v, ∀ t ∈ Set.Icc tp tf,
        IsClassicalRep (u v t) (fun x => Glued G N H CcT aRep t x v) (K + 1)) ∧
      ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
        IsClassicalRep (w v t) (fun x => Glued G N H CcT aRep t x v) (K + 1 + 1) := by
  classical
  subst hm
  have ha := aRep_contDiff_high p Naux K hk η tp tf hΛ hζ Y hhigh PZ aRep hprep
  have ha' : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((K + 2 + N : ℕ) : ℕ∞) (aRep t) := ha
  obtain ⟨u, w, hfield⟩ := native_liftedFieldW_exists_of_prepared_classical_data slotLifts hi hΛ hζ
    hband htorus (K + 2) hres (K + 1) (by omega) hrQ p Naux 0 0 (Nat.zero_le _) (Nat.zero_le _)
    η tp tf Y PZ aRep hprep ha'
  have hreps := native_liftedFieldW_classical_reps slotLifts hi hΛ hζ hband htorus (K + 2) hres
    (K + 1) (by omega) hrQ p Naux 0 0 η tp tf Y _ PZ aRep u w hfield ha'
  have hE (t : ℝ) := Glued_eq_native slotLifts hΛ hζ hband sX sZ CcT hseq aRep t
  refine ⟨u, w, ⟨⟨hseq, hfield.1.2.1, ?_⟩, hfield.2⟩, ?_, ?_⟩
  · intro v t ht
    refine (hfield.1.2.2 v t ht).trans (Filter.Eventually.of_forall fun x => ?_)
    exact congrFun (congrFun (hE t).symm x) v
  · intro v t ht
    have h := hreps.1 v t ht
    rw [hE t]
    exact h
  · intro v
    filter_upwards [hreps.2 v] with t ht
    rw [hE t]
    exact ht

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! **The flux pieces of the bill residual at a cascade frame, from forms shared with the terminal
entry**.

The terminal case proves the three flux bounds (covariance truncation, response boundary, coarse
filter tails) and the fine tail bound by the same outer steps at every passage: an inner flux bound,
the size of the covariance primitive, and a generic operator (`CovTruncOpStatement`,
`CovTruncSubStatement`, `FilterPOpStatement`, all proved in the modules
`EntryTerminal.Ingredients.ResidualFlux.*`). There the outer steps are stated at the terminal
context (`termCovTrunc_of_steps`, `termFrontier_of_steps`, `termFilter_of_steps`,
`termFineTailAt_of_lift_defect`). Their proofs use nothing terminal. This module states them once,
at the arguments of the forms of the residual presentation (a menu, a stage, a window, a radius, a
mass family), and gives the instances at a frame of the covariance transport with the prices of
`succBill`.

Forms (statements, generic over the stage and the menu):
* `CovSizeForm`: `|𝖧(t)| ≤ ωρ²` on the window, `0 ≤ ω ≤ 1`, `𝖧` continuous in time;
* `CovGForm`: `G = menuGFlux` is `C^{k_c+4p}`, periodic, realized at the order `k_c + 4p`;
* `CovGradForm`: `T = (𝖩 - BI)∇(𝒞^p/p!)Z` is realized at the order `k_c`;
* `FrontierInnerForm`, `FilterDefectForm`: the readouts under `P_p`, at the order `k_c + 2p`;
* `FieldRealForm`, `FieldGradEnergyForm`, `StageFineDefectForm`: the lift step and the defect step
  of the fine matrix tail at a classical field.

Assemblies: `covTruncBound_of_forms`, `frontierBound_of_forms`, `filterBound_of_forms`
with the operator constant chosen before the stage, and at a frame `frameCovTrunc_of_forms`,
`frameFrontier_of_forms`, `frameFilter_of_forms`, `frameFineTail_of_lift_defect`.

For `p = 0` one has `ω^p = 1`, the truncation operator is `0` and the covariance truncation
bound is the gradient term alone. For `ω = 0` (no covariance on the window) it is bounded by the
gradient term with `ω^p` (`0` for `p ≥ 1`). For a stage without identities the suprema of the
widths are `0`, the filter and fine prices are `0` for `L_c, L_f ≥ 1`, and the inner statements
hold with the zero realization. For `Ain = 0` every bound is `0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-! ### The forms -/

/-- **Form of the size of the covariance primitive**: `|𝖧(t)| ≤ ωρ²` on the window, with
`0 ≤ ω ≤ 1`, and `𝖧` is continuous in time on the window. The terminal instance is
`CovTruncSizeAt` (`ω = C E^δ`, anchor `t_p`); the cascade instance has `ω` of `succBill`
(`frameOmega`) and the anchor `0`. -/
def CovSizeForm (Mn : SuccMenu) (D : OCData) (m : ℕ) (tp tf ρ ω : ℝ) : Prop :=
  (∀ t ∈ Set.Icc tp tf,
    AVRegularity.CycleComparison.Coarse.covBound (menuCovPrimitive D Mn m t) ≤ ω * ρ ^ 2) ∧
    0 ≤ ω ∧ ω ≤ 1 ∧ ContinuousOn (fun t => menuCovPrimitive D Mn m t) (Set.Icc tp tf)

/-- **Form of the pre-truncation flux**: `G = menuGFlux` is `C^{k_c+4p}`, `ℤ²`-periodic, and
has a realization of order `k_c + 4p` on the window with `B^{-1/2}‖G‖ ≤ Y`. -/
def CovGForm (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p depth kc : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
    (tp tf ρ Y : ℝ) : Prop :=
  (∀ v, ∀ t ∈ Set.Icc tp tf,
    ContDiff ℝ ((kc + 4 * p : ℕ) : ℕ∞) (fun y => menuGFlux Mn G m N p depth CcT aZ v t y) ∧
      IsZ2Periodic (fun y => menuGFlux Mn G m N p depth CcT aZ v t y)) ∧
  HasFluxBound (ι := CompIn G.comps) (h := fun v => hr v.1.root) (kc + 4 * p) (Set.Icc tp tf)
    (D.κ (m - 1)) ρ π (fun v t y => toFluxL (menuGFlux Mn G m N p depth CcT aZ v t y)) Y

/-- **Form of the gradient term**: `T = (𝖩_m - BI)∇(𝒞^p/p!)Z` has a realization of order
`k_c` on the window with `B^{-1/2}‖T‖ ≤ Y`. -/
def CovGradForm (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m p kc : ℕ)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
    (tp tf ρ Y : ℝ) : Prop :=
  HasFluxBound (ι := CompIn G.comps) (h := fun v => hr v.1.root) kc (Set.Icc tp tf)
    (D.κ (m - 1)) ρ π (fun v t y => toFluxL (covTruncGrad Mn G m p aZ v t y)) Y

/-- **Form of the inner flux of the response boundary bound**: the readout of the omitted flux on the omitted rows, on a
classical representative `aY` of the retained solution, is `C^{k_c+2p}`, periodic, and has a
realization of order `k_c + 2p` with `B^{-1/2}‖·‖ ≤ Y`. -/
def FrontierInnerForm (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' Gr : GenStage D hr Dm b j₀) (m p H J kc : ℕ) (E η₀ : ℝ)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
    (tp tf ρ Y : ℝ) : Prop :=
  (∀ v, ∀ t ∈ Set.Icc tp tf,
    ContDiff ℝ ((kc + 2 * p : ℕ) : ℕ∞)
        (fun y => frontierReadout P seedK freshK φ₀ G G' Gr m H J E η₀ aY v t y) ∧
      IsZ2Periodic (fun y => frontierReadout P seedK freshK φ₀ G G' Gr m H J E η₀ aY v t y)) ∧
  HasFluxBound (ι := CompIn G.comps) (h := fun v => hr v.1.root) (kc + 2 * p) (Set.Icc tp tf)
    (D.κ (m - 1)) ρ π
    (fun v t y => toFluxL (frontierReadout P seedK freshK φ₀ G G' Gr m H J E η₀ aY v t y)) Y

/-- **Form of the inner flux of the coarse filter tails bound**: the readout of the root flux defects of the successor, on a
classical representative `aZ` of the readout, is `C^{k_c+2p}`, periodic, and has a realization of
order `k_c + 2p` with `B^{-1/2}‖·‖ ≤ Y`. -/
def FilterDefectForm (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' : GenStage D hr Dm b j₀) (m p kc : ℕ) (E η₀ : ℝ)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
    (tp tf ρ Y : ℝ) : Prop :=
  (∀ v, ∀ t ∈ Set.Icc tp tf,
    ContDiff ℝ ((kc + 2 * p : ℕ) : ℕ∞)
        (fun y => filterReadoutDefect P seedK freshK φ₀ G G' m E η₀ aZ v t y) ∧
      IsZ2Periodic (fun y => filterReadoutDefect P seedK freshK φ₀ G G' m E η₀ aZ v t y)) ∧
  HasFluxBound (ι := CompIn G.comps) (h := fun v => hr v.1.root) (kc + 2 * p) (Set.Icc tp tf)
    (D.κ (m - 1)) ρ π
    (fun v t y => toFluxL (filterReadoutDefect P seedK freshK φ₀ G G' m E η₀ aZ v t y)) Y

/-- **Form of the lift step of the fine tail bound, the representative**: `Û` is a torus Sobolev representative of
order `K + 1` of the classical field `uh` on the window: square integrable in time, at every time
of the window its value jet is `uh` almost everywhere on the cell, and `uh` is `C^{K+1}` and
periodic there. -/
def FieldRealForm (G : GenStage D hr Dm b j₀) (K : ℕ) (tp tf : ℝ)
    (uh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (Û : ∀ v : CompIn G.comps, ℝ → TorusHk (K + 1) (hr v.1.root)) : Prop :=
  (∀ v, MemLp (Û v) 2 (volume.restrict (Set.Icc tp tf))) ∧
  (∀ v, ∀ t ∈ Set.Icc tp tf,
    (Û v t).toFunction.jet (valueIndex2 (K + 1)) =ᵐ[volume.restrict unitCube]
      fun x => uh t x v) ∧
  (∀ v, ∀ t ∈ Set.Icc tp tf,
    ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (fun x => uh t x v) ∧ IsZ2Periodic (fun x => uh t x v))

/-- **Form of the lift step of the fine tail bound, the energy**: `t ↦ |∇Û|²_{ρ,K;π}` is integrable on the window
and `(ν ∫_I |∇Û|²_{ρ,K;π})^{1/2} ≤ E`. -/
def FieldGradEnergyForm (G : GenStage D hr Dm b j₀) (K : ℕ) (ν ρ : ℝ)
    (π : CompIn G.comps → ℝ) (tp tf : ℝ)
    (Û : ∀ v : CompIn G.comps, ℝ → TorusHk (K + 1) (hr v.1.root)) (E : ℝ) : Prop :=
  Integrable (fun s => massGradNormSq (E := fun v : CompIn G.comps => hr v.1.root)
      (K := fun _ => K) ρ π (fun v => (Û v s).val)) (volume.restrict (Set.Icc tp tf)) ∧
  Real.sqrt (ν * ∫ s in Set.Icc tp tf,
    massGradNormSq (E := fun v : CompIn G.comps => hr v.1.root) (K := fun _ => K) ρ π
      (fun v => (Û v s).val)) ≤ E

/-- **Form of the defect step of the fine tail bound** (the generic restatement of `fineDefectAt_of`): for every classical field `uh`
with a representative `Û` of order `K + 1` and gradient energy at most `E`, the fine flux
`∑ 𝖠 ∇^{d-1}(I - S)uh` of the stage has a realization of order `k` with
`(ν⁻¹∫_I ‖·‖²_{r_s,k;π})^{1/2} ≤ Y·E`. The price `Y` is `C·θ_K·ε_f^{L_f}` at a stage whose
invariant has the Schur bound `θ_K` and whose kernels have `L_f` vanishing moments and widths at
most `ε_f r_s`; the order is `K ≥ k + (D_m - 2) + L_f`. -/
def StageFineDefectForm (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G : GenStage D hr Dm b j₀) (m k K : ℕ) (π : CompIn G.comps → ℝ) (tp tf rs Y : ℝ) : Prop :=
  ∀ (uh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (Û : ∀ v : CompIn G.comps, ℝ → TorusHk (K + 1) (hr v.1.root)) (E : ℝ),
    FieldRealForm G K tp tf uh Û → FieldGradEnergyForm G K (D.κ m) rs π tp tf Û E →
    HasFluxBound (ι := CompIn G.comps) (h := fun v => hr v.1.root) k (Set.Icc tp tf) (D.κ m) rs π
      (fineFluxF P seedK freshK φ₀ G uh) (Y * E)

/-! ### The generic assemblies -/

/-- The price of the two terms of the covariance truncation:
`C_op ω^{p+1}(C₁A) + C₁ω^pA ≤ (C_opC₁ + C₁)(ω^p + ω^{p+1})A`. -/
theorem cov_price_le {Cop C₁ w w' A : ℝ} (hCop : 0 ≤ Cop) (hC₁ : 0 ≤ C₁) (hw : 0 ≤ w)
    (hw' : 0 ≤ w') (hA : 0 ≤ A) :
    Cop * w' * (C₁ * A) + C₁ * w * A ≤ (Cop * C₁ + C₁) * (w + w') * A := by
  have h1 : 0 ≤ Cop * C₁ * w * A := mul_nonneg (mul_nonneg (mul_nonneg hCop hC₁) hw) hA
  have h2 : 0 ≤ C₁ * w' * A := mul_nonneg (mul_nonneg hC₁ hw') hA
  have e : (Cop * C₁ + C₁) * (w + w') * A =
      Cop * w' * (C₁ * A) + C₁ * w * A + (Cop * C₁ * w * A + C₁ * w' * A) := by ring
  rw [e]
  linarith

/-- **The covariance truncation bound from its forms, generic over the stage and the menu** (the generic restatement of
`termCovTrunc_of_steps`). The
operator constant depends on `k_c` and `p` only. -/
theorem covTruncBound_of_forms (hOp : CovTruncOpStatement) (hSub : CovTruncSubStatement)
    (kc p : ℕ) : ∃ Cop : ℝ, 0 ≤ Cop ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
      (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
      (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
      (tp tf ρ ω YG YT : ℝ), 0 < D.κ (m - 1) → 0 < ρ → (∀ v, 0 < π v) →
      CovSizeForm Mn D m tp tf ρ ω → CovGForm Mn G m N p depth kc CcT aZ π tp tf ρ YG →
      CovGradForm Mn G m p kc aZ π tp tf ρ YT →
      CovTruncBound Mn G m N p depth kc CcT aZ π tp tf ρ (Cop * ω ^ (p + 1) * YG + YT) := by
  obtain ⟨Cop, hCop, hOp'⟩ := hOp kc p
  refine ⟨Cop, hCop, ?_⟩
  intro hr _ _ _ _ _ _ D Dm b j₀ Mn G m N depth CcT aZ π tp tf ρ ω YG YT hν hρ hπ hS hG hT
  obtain ⟨hsz, hω0, hω1, hcont⟩ := hS
  obtain ⟨hGreg, hG'⟩ := hG
  have hop := hOp' (ι := CompIn G.comps) (h := fun v => hr v.1.root)
    (Set.Icc tp tf) measurableSet_Icc (D.κ (m - 1)) ρ π hν hρ hπ
    (fun t => menuCovPrimitive D Mn m t) ω hcont hω0 hω1 hsz
    (fun v t y => menuGFlux Mn G m N p depth CcT aZ v t y) YG hGreg hG'
  have hsub := hSub kc (Set.Icc tp tf) (D.κ (m - 1)) ρ π hν hπ _ _ _ _ hop hT
  have hfun : (fun (v : CompIn G.comps) (t : ℝ) (y : Vec 2) => toFluxL
      (menuCovTruncFlux Mn G m N p depth CcT aZ v t y)) =
      fun v t y => toFluxL
        (menuGFlux Mn G m N p depth CcT aZ v t y -
          covPolyP (menuCovPrimitive D Mn m t) p
            (covPolyQ (menuCovPrimitive D Mn m t) p
              (fun z => menuGFlux Mn G m N p depth CcT aZ v t z)) y) -
        toFluxL (covTruncGrad Mn G m p aZ v t y) := by
    funext v t y
    rw [menuCovTruncFlux_eq_sub]
    exact WithLp.toLp_sub 2 _ _
  unfold CovTruncBound
  rw [hfun]
  exact hsub

/-- **The response boundary bound from its forms, generic over the stage and the menu** (the generic restatement of
`termFrontier_of_steps`). -/
theorem frontierBound_of_forms (hP : FilterPOpStatement) (kc p : ℕ) : ∃ Cp : ℝ, 0 ≤ Cp ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
      (Mn : SuccMenu) (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
      (G G' Gr : GenStage D hr Dm b j₀) (m H J : ℕ) (E η₀ : ℝ)
      (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
      (tp tf ρ ω Y : ℝ), 0 < D.κ (m - 1) → 0 < ρ → (∀ v, 0 < π v) →
      CovSizeForm Mn D m tp tf ρ ω →
      FrontierInnerForm P seedK freshK φ₀ G G' Gr m p H J kc E η₀ aY π tp tf ρ Y →
      FrontierBound Mn P seedK freshK φ₀ G G' Gr m p H J kc E η₀ aY π tp tf ρ (Cp * Y) := by
  obtain ⟨Cp, hCp, hP'⟩ := hP kc p
  refine ⟨Cp, hCp, ?_⟩
  intro hr _ _ _ _ _ _ D Dm b j₀ Mn P seedK freshK φ₀ G G' Gr m H J E η₀ aY π tp tf ρ ω Y hν hρ hπ
    hS hF
  obtain ⟨hsz, hω0, hω1, hcont⟩ := hS
  obtain ⟨hreg, hF'⟩ := hF
  exact hP' (ι := CompIn G.comps) (h := fun v => hr v.1.root)
    (Set.Icc tp tf) measurableSet_Icc (D.κ (m - 1)) ρ π hν hρ hπ
    (fun t => menuCovPrimitive D Mn m t) ω hcont hω0 hω1 hsz
    (fun v t y => frontierReadout P seedK freshK φ₀ G G' Gr m H J E η₀ aY v t y) Y hreg hF'

/-- **The coarse filter tails bound from its forms, generic over the stage and the menu** (the generic restatement of
`termFilter_of_steps`). -/
theorem filterBound_of_forms (hP : FilterPOpStatement) (kc p : ℕ) : ∃ Cp : ℝ, 0 ≤ Cp ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
      (Mn : SuccMenu) (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
      (G G' : GenStage D hr Dm b j₀) (m : ℕ) (E η₀ : ℝ)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
      (tp tf ρ ω Y : ℝ), 0 < D.κ (m - 1) → 0 < ρ → (∀ v, 0 < π v) →
      CovSizeForm Mn D m tp tf ρ ω →
      FilterDefectForm P seedK freshK φ₀ G G' m p kc E η₀ aZ π tp tf ρ Y →
      FilterBound Mn P seedK freshK φ₀ G G' m p kc E η₀ aZ π tp tf ρ (Cp * Y) := by
  obtain ⟨Cp, hCp, hP'⟩ := hP kc p
  refine ⟨Cp, hCp, ?_⟩
  intro hr _ _ _ _ _ _ D Dm b j₀ Mn P seedK freshK φ₀ G G' m E η₀ aZ π tp tf ρ ω Y hν hρ hπ hS hF
  obtain ⟨hsz, hω0, hω1, hcont⟩ := hS
  obtain ⟨hreg, hF'⟩ := hF
  exact hP' (ι := CompIn G.comps) (h := fun v => hr v.1.root)
    (Set.Icc tp tf) measurableSet_Icc (D.κ (m - 1)) ρ π hν hρ hπ
    (fun t => menuCovPrimitive D Mn m t) ω hcont hω0 hω1 hsz
    (fun v t y => filterReadoutDefect P seedK freshK φ₀ G G' m E η₀ aZ v t y) Y hreg hF'

/-! ### The instances at a frame -/

section Frame

variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- `ω = ‖𝖧‖_∞/ρ²` of `succBill` at the frame. -/
def frameOmega (cr : ℝ) : ℝ :=
  (⨆ t : Set.Icc F.tp F.tf, ∑ a : Fin 2, ∑ a' : Fin 2, |covPrimitive D F.m t a a'|) /
    rhoEnh D cr F.m ^ 2

/-- The price of the covariance truncation is `ω^p + ω^{p+1}`. -/
theorem succCovPrice_eq (cr : ℝ) :
    succCovPrice D F.m cr F.p F.tp F.tf = frameOmega F cr ^ F.p + frameOmega F cr ^ (F.p + 1) :=
  rfl

/-- **The lift step of the fine tail bound at a frame** (the
`successor_full_lift_bound` at the order `K + 1`): the lifted field has a representative of order
`K + 1` with the gradient energy `≤ C·A_in` at the radius `ρ_⋆`. -/
def FrameFineLiftAt (c₀ : ℝ) (K : ℕ) (Ain C : ℝ) : Prop :=
  ∃ Û : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K + 1) (hr v.1.root),
    FieldRealForm F.G K F.tp F.tf (menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep) Û ∧
    FieldGradEnergyForm F.G K (D.κ F.m) (rhoStar D c₀ F.m) (F.G.mass law) F.tp F.tf Û (C * Ain)

/-- **The defect step of the fine tail bound at a frame**: the fine defect of every
represented classical field costs `C·ε_f^{L_f}` times its gradient energy. -/
def FrameFineDefectAt (c₀ : ℝ) (Lf K : ℕ) (C : ℝ) : Prop :=
  StageFineDefectForm F.P F.seedK F.freshK F.φ₀ F.G F.m 0 K (F.G.mass law) F.tp F.tf
    (rhoStar D c₀ F.m) (C * succFineBill D F.G F.m c₀ Lf)

/-- **The fine tail bound at a frame from the lift step and the defect step.** -/
theorem frameFineTail_of_lift_defect {c₀ : ℝ} {Lf K : ℕ} {Ain C₁ C₂ : ℝ}
    (hL : FrameFineLiftAt F law c₀ K Ain C₁) (hD : FrameFineDefectAt F law c₀ Lf K C₂) :
    FrameFineTailAt F law c₀ Lf Ain (C₂ * C₁) := by
  obtain ⟨Û, hr', he⟩ := hL
  have h := hD _ Û _ hr' he
  unfold FrameFineTailAt FineTailBound
  exact hasFluxBound_mono_Y h (le_of_eq (by ring))

end Frame

/-- **The covariance truncation bound at a frame from its forms**, with the price `ω^p + ω^{p+1}` of `succBill`. The operator
constant is chosen before the frame. -/
theorem frameCovTrunc_of_forms (hOp : CovTruncOpStatement) (hSub : CovTruncSubStatement)
    (kc p : ℕ) : ∃ Cop : ℝ, 0 ≤ Cop ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
      (F : Frame D hr Dm b j₀) (law : BirthLaw), F.p = p →
      ∀ (cr Ain C₁ : ℝ), 0 < D.κ (F.m - 1) → 0 < rhoEnh D cr F.m →
        (∀ v, 0 < F.G.mass law v) → 0 ≤ Ain → 0 ≤ C₁ →
      CovSizeForm F.Mn D F.m F.tp F.tf (rhoEnh D cr F.m) (frameOmega F cr) →
      CovGForm F.Mn F.G F.m F.N F.p F.depth kc F.CcT F.aZ (F.G.mass law) F.tp F.tf
        (rhoEnh D cr F.m) (C₁ * Ain) →
      CovGradForm F.Mn F.G F.m F.p kc F.aZ (F.G.mass law) F.tp F.tf (rhoEnh D cr F.m)
        (C₁ * frameOmega F cr ^ F.p * Ain) →
      FrameCovTruncAt F law kc cr Ain (Cop * C₁ + C₁) := by
  obtain ⟨Cop, hCop, hgen⟩ := covTruncBound_of_forms hOp hSub kc p
  refine ⟨Cop, hCop, ?_⟩
  intro hr _ _ _ _ _ _ D Dm b j₀ F law hp cr Ain C₁ hν hρ hπ hA hC₁ hS hG hT
  subst hp
  have h := hgen F.Mn F.G F.m F.N F.depth F.CcT F.aZ (F.G.mass law) F.tp F.tf (rhoEnh D cr F.m)
    (frameOmega F cr) (C₁ * Ain) (C₁ * frameOmega F cr ^ F.p * Ain) hν hρ hπ hS hG hT
  unfold CovTruncBound at h
  unfold FrameCovTruncAt CovTruncBound
  refine hasFluxBound_mono_Y h ?_
  rw [succCovPrice_eq]
  have hω : 0 ≤ frameOmega F cr := hS.2.1
  exact cov_price_le hCop hC₁ (pow_nonneg hω _) (pow_nonneg hω _) hA

/-- **The response boundary bound at a frame from its forms**, with the price `E^{ιΣ_H} + E^{θ₁+Jθ₂}` of `succBill`. -/
theorem frameFrontier_of_forms (hP : FilterPOpStatement) (kc p : ℕ) : ∃ Cp : ℝ, 0 ≤ Cp ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
      (F : Frame D hr Dm b j₀) (law : BirthLaw), F.p = p →
      ∀ (cr θ₁ θ₂ ω Ain C₁ : ℝ), 0 < D.κ (F.m - 1) → 0 < rhoEnh D cr F.m →
        (∀ v, 0 < F.G.mass law v) →
      CovSizeForm F.Mn D F.m F.tp F.tf (rhoEnh D cr F.m) ω →
      FrontierInnerForm F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.p F.H F.J kc
        (D.eps (F.m - 1)) F.η₀ F.aY (F.G.mass law) F.tp F.tf (rhoEnh D cr F.m)
        (C₁ * succFrontPrice D F.m F.η₀ F.J F.H θ₁ θ₂ * Ain) →
      FrameFrontierAt F law kc cr θ₁ θ₂ Ain (Cp * C₁) := by
  obtain ⟨Cp, hCp, hgen⟩ := frontierBound_of_forms hP kc p
  refine ⟨Cp, hCp, ?_⟩
  intro hr _ _ _ _ _ _ D Dm b j₀ F law hp cr θ₁ θ₂ ω Ain C₁ hν hρ hπ hS hF
  subst hp
  have h := hgen F.Mn F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.H F.J (D.eps (F.m - 1)) F.η₀
    F.aY (F.G.mass law) F.tp F.tf (rhoEnh D cr F.m) ω _ hν hρ hπ hS hF
  unfold FrontierBound at h
  unfold FrameFrontierAt FrontierBound
  exact hasFluxBound_mono_Y h (le_of_eq (by ring))

/-- **The coarse filter tails bound at a frame from its forms**, with the price `ε_o^{L_c}` of `succBill`. -/
theorem frameFilter_of_forms (hP : FilterPOpStatement) (kc p : ℕ) : ∃ Cp : ℝ, 0 ≤ Cp ∧
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
      (F : Frame D hr Dm b j₀) (law : BirthLaw), F.p = p →
      ∀ (cr σ₀ : ℝ) (Lc : ℕ) (ω Ain C₁ : ℝ), 0 < D.κ (F.m - 1) → 0 < rhoEnh D cr F.m →
        (∀ v, 0 < F.G.mass law v) →
      CovSizeForm F.Mn D F.m F.tp F.tf (rhoEnh D cr F.m) ω →
      FilterDefectForm F.P F.seedK F.freshK F.φ₀ F.G F.G' F.m F.p kc (D.eps (F.m - 1)) F.η₀
        F.aZ (F.G.mass law) F.tp F.tf (rhoEnh D cr F.m)
        (C₁ * succFilterPrice D F.G F.m cr σ₀ Lc * Ain) →
      FrameFilterAt F law kc cr σ₀ Lc Ain (Cp * C₁) := by
  obtain ⟨Cp, hCp, hgen⟩ := filterBound_of_forms hP kc p
  refine ⟨Cp, hCp, ?_⟩
  intro hr _ _ _ _ _ _ D Dm b j₀ F law hp cr σ₀ Lc ω Ain C₁ hν hρ hπ hS hF
  subst hp
  have h := hgen F.Mn F.P F.seedK F.freshK F.φ₀ F.G F.G' F.m (D.eps (F.m - 1)) F.η₀
    F.aZ (F.G.mass law) F.tp F.tf (rhoEnh D cr F.m) ω _ hν hρ hπ hS hF
  unfold FilterBound at h
  unfold FrameFilterAt FilterBound
  exact hasFluxBound_mono_Y h (le_of_eq (by ring))

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
