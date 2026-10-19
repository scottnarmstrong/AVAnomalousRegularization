-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
public import AVRegularity.Construction.Preservation.Buffer.ShiftedEnergyEndpoint
public import AVRegularity.Definitions.Construction.ScheduleFloor
import AVRegularity.Construction.Scales.Times
public import AVRegularity.CycleJoint.ConstituentPhysicalOrderSupport
import AVRegularity.Families.TorusCompatible.WeakStage
public import AVRegularity.KernelEnergy.TorusKernelFiniteTraceLimit
import AVRegularity.KernelEnergy.TorusKernelResidualODE
import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
import AVRegularity.CycleJoint.UnitPatchValuePeriodization
public import AVRegularity.Statements.Construction.IsOCStreamSeq
import AVRegularity.Velocity.IncrementProvider
import AVenhance.Infra.Flow.GradientDeviation
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.Buffer

/-! A Fourier test needs a unit direction only when some actual component is nontrivial. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]

theorem component_hilbert_dichotomy (S : Finset Comp) :
    (∀ v : CompIn S, Subsingleton (hr v.1.root)) ∨
      ∃ (v : CompIn S) (e : hr v.1.root), ‖e‖ = 1 := by
  classical
  by_cases h : ∀ v : CompIn S, Subsingleton (hr v.1.root)
  · exact Or.inl h
  · push Not at h
    obtain ⟨v, hv⟩ := h
    have componentNontrivial : Nontrivial (hr v.1.root) := hv
    obtain ⟨e, he⟩ := exists_norm_eq (hr v.1.root) (by norm_num : (0 : ℝ) ≤ 1)
    exact Or.inr ⟨v, e, he⟩

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! At order zero the weighted initial mass is independent of the molecular radius. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem weightedNorm_order_zero_radius {S : Finset Comp} (ρ R : ℝ)
    (π w : CompIn S → ℝ) (f : ∀ v : CompIn S, TorusHk 0 (hr v.1.root)) :
    weightedNorm ρ π w f = weightedNorm R π w f := by
  unfold weightedNorm massNormSq
  simp only [factorialNormSq_zero_eq_derivative]
end

/-! Convert the molecular mass estimate into the weighted norm of the statement. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem weighted_buffer_readout {S : Finset Comp} (ρ : ℝ) (j : ℕ)
    (π w : CompIn S → ℝ) (f : ∀ v : CompIn S, TorusHk 0 (hr v.1.root))
    (W : ∀ v : CompIn S, TorusHk j (hr v.1.root))
    (hW : Real.sqrt (massNormSq ρ (fun v => π v / w v ^ 2) (fun v => (W v).val)) ≤
      Real.sqrt (bufferEnergyCost j *
        massNormSq ρ (fun v => π v / w v ^ 2) (fun v => (f v).val))) :
    weightedNorm ρ π w W ≤ Real.sqrt (bufferEnergyCost j) * weightedNorm 1 π w f := by
  change weightedNorm ρ π w W ≤ _ at hW
  rw [Real.sqrt_mul (bufferEnergyCost_nonneg j)] at hW
  change weightedNorm ρ π w W ≤ Real.sqrt (bufferEnergyCost j) * weightedNorm ρ π w f at hW
  rw [weightedNorm_order_zero_radius ρ 1 π w f] at hW
  exact hW
end

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Trivial component Hilbert spaces require neither a test direction nor a positive wait. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusHk_eq_zero_of_subsingleton (hE : Subsingleton E) {K : ℕ} (u : TorusHk K E) :
    u = 0 := by
  have subsingletonE : Subsingleton E := hE
  apply Subtype.ext
  apply PiLp.ext
  intro j
  apply Lp.ext
  exact Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem weightedNorm_zero {S : Finset Comp} (K : ℕ) (ρ : ℝ) (π w : CompIn S → ℝ) :
    weightedNorm ρ π w (fun v => (0 : TorusHk K (hr v.1.root))) = 0 := by
  unfold weightedNorm
  rw [show (fun v : CompIn S => (0 : TorusHk K (hr v.1.root)).val) = 0 from rfl,
    CycleJointProofs.massNormSq_zero, Real.sqrt_zero]

theorem subsingleton_carrier_buffer {S : Finset Comp}
    (hS : ∀ v : CompIn S, Subsingleton (hr v.1.root))
    (K : ℕ) (ρ : ℝ) (π w : CompIn S → ℝ)
    (U : ∀ v : CompIn S, TorusHk 0 (hr v.1.root)) :
    ∃ W : ∀ v : CompIn S, TorusHk K (hr v.1.root),
      (∀ v, truncateTorusHk (Nat.zero_le K) (W v) = U v) ∧ weightedNorm ρ π w W = 0 := by
  refine ⟨fun _ => 0, ?_, weightedNorm_zero K ρ π w⟩
  intro v
  rw [map_zero, torusHk_eq_zero_of_subsingleton (hS v) (U v)]

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Grade allocation leaves a positive native analytic reserve above the envelope reserve. -/

theorem compReserve_le_one (k : InvConsts) (c : Comp) : compReserve k c ≤ 1 := by
  unfold compReserve
  have hh : 0 ≤ ((k.G0 + compGrade c : ℕ) : ℝ) / ((k.Hprod : ℝ) + 1) := by positivity
  linarith only [hh]

theorem compReserve_ge_allocated_gap (k : InvConsts) (H : ℕ)
    (hk : k.Hprod = k.G0 + H + 1) (c : Comp) (hc : compGrade c ≤ H + 1) :
    1 / ((k.Hprod : ℝ) + 1) ≤ compReserve k c := by
  have hd : 0 < (k.Hprod : ℝ) + 1 := by positivity
  have he : compReserve k c =
      (((k.Hprod : ℝ) + 1) - (k.G0 + compGrade c : ℕ)) / ((k.Hprod : ℝ) + 1) := by
    unfold compReserve
    rw [sub_div, div_self hd.ne']
  rw [he]
  apply div_le_div_of_nonneg_right _ hd.le
  have hh : (compGrade c : ℝ) ≤ (H : ℝ) + 1 := by exact_mod_cast hc
  rw [hk]
  push_cast
  linarith only [hh]

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual native certificate's real semantics inherits its flux's fast torus period. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_context_sem_periodic
    (G : GenStage D hr Dm bw j₀) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2) (t : ℝ) (f : GenSort.Sem .ctx)
    (he : ∀ (ctx : StageCtx D bw j₀ G.level p) (X z : Vec 2),
      G.fam.flux p ctx v u γ d I t X z c =
        if IsAdmissibleChain D bw j₀ G.level p.1
            (ctx.1.recenter D (D.eps (G.level - 1) • X))
        then f t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0)
    (Y : Vec 2) :
    IsZ2Periodic (fun z => f t ⟨G.level - 1, [p.1], Y, []⟩ z) := by
  let ch : RealChain := ⟨G.level - 1, [p.1], Y, []⟩
  have ha : IsAdmissibleChain D bw j₀ G.level p.1 ch :=
    nativeChain_isCarrier D bw j₀ G.level p.1 2 hi hj p.2 Y
  let ctx : StageCtx D bw j₀ G.level p := ⟨ch, ha⟩
  have hrec : ctx.1.recenter D (D.eps (G.level - 1) • (0 : Vec 2)) = ch := by
    simp only [ctx, ch, RealChain.recenter, smul_zero, add_zero]
    rfl
  have heq (z : Vec 2) : G.fam.flux p ctx v u γ d I t 0 z c = f t ch z := by
    have hh := he ctx 0 z
    rw [hrec, ite_eq_left ha] at hh
    exact hh
  intro n z
  change f t ch (z + latticeShift n) = f t ch z
  rw [← heq, ← heq]
  exact congrArg (fun z : Vec 2 => z c) (G.fam.flux_periodic p ctx v u γ d I t 0 n z)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Retention bounds every incoming component grade, leaving a positive native reserve. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem cascade_component_grade_le
    {P : ProvParams} {Mn : SuccMenu} {seed G : GenStage D hr Dm bw j₀}
    (hseed : ∀ v : CompIn seed.comps, v.1.births = [])
    (hc : IsCascadeStage D P Mn seed G) (v : CompIn G.comps) :
    compGrade v.1 ≤ Mn.H := by
  induction hc with
  | seed =>
    simp only [compGrade, hseed v, List.length_nil]
    exact Nat.zero_le _
  | @step G G' _ _ _ =>
    exact (Finset.mem_filter.mp v.2).2.1

theorem cascade_component_reserve_pos
    {P : ProvParams} {Mn : SuccMenu} {seed G : GenStage D hr Dm bw j₀}
    (hseed : ∀ v : CompIn seed.comps, v.1.births = [])
    (hc : IsCascadeStage D P Mn seed G) (k : InvConsts)
    (hk : k.Hprod = k.G0 + Mn.H + 1) (v : CompIn G.comps) :
    0 < compReserve k v.1 := by
  have hgap := compReserve_ge_allocated_gap k Mn.H hk v.1
    ((cascade_component_grade_le hseed hc v).trans (Nat.le_succ _))
  exact (by positivity : 0 < 1 / ((k.Hprod : ℝ) + 1)).trans_le hgap

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Buffer

/-! The incoming certificate supplies scalar time measurability of its literal fluxes. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem contextCertified_flux_time_measurable {k : InvConsts}
    {G : GenStage D hr Dm b j₀} (hG : G.IsContextCertified k)
    (p : OddSlot) (ctx : StageCtx D b j₀ G.level p)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (α : AVRegularity.Sobolev.DerivativeWord2 (d - 1)) (c : Fin 2) (X z : Vec 2) :
    Measurable (fun t : ocPulseWindow D.α D.q D.Λ G.level p.1 =>
      G.fam.flux p ctx v u γ d α t X z c) := by
  obtain ⟨_, _, _, hforms⟩ := hG v u γ
  obtain ⟨f, F, hslots, _⟩ := hforms d α c
  obtain ⟨_, hF, heq⟩ := hslots p
  let ch := ctx.1.recenter D (D.eps (G.level - 1) • X)
  by_cases hch : IsAdmissibleChain D b j₀ G.level p.1 ch
  · have hm := holExtension_time_measurable hF ch hch z
    have he : (fun t : ocPulseWindow D.α D.q D.Λ G.level p.1 =>
        G.fam.flux p ctx v u γ d α t X z c) = (fun t : ocPulseWindow D.α D.q D.Λ G.level p.1 => f p t ch z) := by
      funext t
      simpa only [ch, ite_eq_left hch] using heq ctx t t.property X z
    rw [he]
    exact hm
  · have he : (fun t : ocPulseWindow D.α D.q D.Λ G.level p.1 =>
        G.fam.flux p ctx v u γ d α t X z c) = (fun _ => (0 : ℝ)) := by
      funext t
      simpa only [ch, ite_eq_right hch] using heq ctx t t.property X z
    rw [he]
    exact measurable_const

theorem contextCertified_flux_time_measurable_vec {k : InvConsts}
    {G : GenStage D hr Dm b j₀} (hG : G.IsContextCertified k)
    (p : OddSlot) (ctx : StageCtx D b j₀ G.level p)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (α : AVRegularity.Sobolev.DerivativeWord2 (d - 1)) (X z : Vec 2) :
    Measurable (fun t : ocPulseWindow D.α D.q D.Λ G.level p.1 =>
      G.fam.flux p ctx v u γ d α t X z) := by
  exact Measurable.of_eval (fun c =>
    contextCertified_flux_time_measurable hG p ctx v u γ d α c X z)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.Construction.Preservation.Buffer

/-! Time fields need measurability only on the pulse supporting their weight. -/

theorem measurable_weighted_local_field {S : Set ℝ} (hS : MeasurableSet S)
    (w : ℝ → ℝ) (f : ℝ → Vec 2) (hw : Measurable w)
    (hzero : ∀ t, t ∉ S → w t = 0)
    (hf : Measurable (fun t : S => f t)) :
    Measurable (fun t => w t • f t) := by
  apply measurable_of_restrict_of_restrict_compl hS
  · exact (hw.comp measurable_subtype_coe).smul hf
  · have he : (fun t : (Sᶜ : Set ℝ) => w t • f t) = (fun _ => (0 : Vec 2)) := by
      funext t
      rw [hzero t t.property, zero_smul]
    change Measurable (fun t : (Sᶜ : Set ℝ) => w t • f t)
    rw [he]
    exact measurable_const

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! The existing allocation supplies a positive preparation order, even for a zero-order buffer. -/

theorem preparation_schedule_output_positive {α q s Q σ₀ a σ σf lamC : ℝ}
    {D₀ H J N p nk Lc Lf Lpr Acl Naux Nout : ℕ}
    (hs : IsSuccessorSchedule α q s Q σ₀ a σ σf lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout) :
    1 ≤ Nout := by
  have halloc : Naux + 4 * p ≤ Nout := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hp : 1 ≤ p := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  omega

theorem preparation_schedule_order_ge_two (D₀ N p H : ℕ) :
    2 ≤ succSchedD D₀ N p (H + 1) := by
  change 2 ≤ succSchedD D₀ N p H + 2 * N + 4 * p + 4
  omega

theorem invariantAdmissible_molecular_parameters {kS thr kI : InvConsts}
    {H J N p nk Kres Lpr Lc Lf : ℕ} {σ₀ δ q c : ℝ}
    (hk : IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ δ q c) :
    kI.c₀ = kS.c₀ ∧ kI.cr = kS.cr ∧ kI.Hprod = kI.G0 + H + 1 := by
  exact ⟨hk.1, hk.2.1, hk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Joint coefficient measurability from time measurability only on the supporting pulse. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem weighted_dimFlux_joint_measurable_on_domain
    (F : ChartedFamily ι h D P Ctx) (ν e E tS tZ : ℝ) (n : ι → ℕ)
    (dom : F.Domain) (hs : F.IsSmoothOn dom E n)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1))
    (hdom : ∀ t ∈ (F.piece p).output ∩ Set.Icc tS tZ, ∀ Y, (t, Y) ∈ dom p c)
    {S : Set ℝ} (hS : MeasurableSet S) (hw : Measurable (F.weight p))
    (hzero : ∀ t, t ∉ S → F.weight p t = 0)
    (hm : ∀ X z, Measurable (fun t : S => F.flux p c v u γ d I t X z)) :
    Measurable (fun z : Set.Icc tS tZ × (Vec 2 × Vec 2) =>
      F.weight p z.1 • F.dimFlux ν e E p c v u γ d I z.1 z.2.1 z.2.2) := by
  have hc (t : Set.Icc tS tZ) : Continuous (fun yz : Vec 2 × Vec 2 =>
      F.weight p t • F.dimFlux ν e E p c v u γ d I t yz.1 yz.2) := by
    simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux, smul_smul]
    by_cases hwzero : F.weight p t = 0
    · simp only [hwzero, zero_mul, zero_smul]
      exact continuous_const
    have hout : (t : ℝ) ∈ (F.piece p).output := by
      by_contra hout
      exact hwzero (F.weight_zero p t hout)
    apply continuous_iff_continuousAt.mpr
    intro yz
    have hr : ContinuousAt (fun q : Vec 2 × Vec 2 => F.flux p c v u γ d I t q.1 q.2)
        (E⁻¹ • yz.1, yz.2) :=
      (hs p c v u γ d I (t, yz.1) (hdom t ⟨hout, t.property⟩ yz.1) yz.2).continuousAt
    have hmap : Continuous (fun q : Vec 2 × Vec 2 => (E⁻¹ • q.1, q.2)) :=
      (continuous_fst.const_smul (E⁻¹)).prodMk continuous_snd
    have hcomp : ContinuousAt
        (fun q : Vec 2 × Vec 2 => F.flux p c v u γ d I t (E⁻¹ • q.1) q.2) yz :=
      ContinuousAt.comp (f := fun q : Vec 2 × Vec 2 => (E⁻¹ • q.1, q.2))
        (g := fun q : Vec 2 × Vec 2 => F.flux p c v u γ d I t q.1 q.2) hr hmap.continuousAt
    exact hcomp.const_smul (F.weight p t * (ν * e ^ (d - 2)))
  have ht (yz : Vec 2 × Vec 2) : Measurable (fun t : Set.Icc tS tZ =>
      F.weight p t • F.dimFlux ν e E p c v u γ d I t yz.1 yz.2) := by
    have hf := measurable_weighted_local_field hS (F.weight p)
      (fun t => F.flux p c v u γ d I t (E⁻¹ • yz.1) yz.2)
      hw hzero (hm (E⁻¹ • yz.1) yz.2)
    have hscaled : Measurable (fun t : Set.Icc tS tZ =>
        (ν * e ^ (d - 2)) • (F.weight p t •
          F.flux p c v u γ d I t (E⁻¹ • yz.1) yz.2)) :=
      (hf.const_smul (ν * e ^ (d - 2))).comp measurable_subtype_coe
    simpa only [ChartedFamily.dimFlux, ChartedFamily.slowFlux, smul_smul,
      mul_comm] using hscaled
  exact (measurable_uncurry_of_continuous_of_measurable hc ht).comp measurable_swap
end

/-! Every continuous finite coefficient curve has an integrable actual kernel ODE right side. -/

section
open CoupledEnergy.Galerkin KernelEnergy
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν : ℝ} {k D : ℕ}

theorem kernel_curve_rhs_intervalIntegrable
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
    (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N)) :
    IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (P.projectedMatrix N v t)) (fun _ => 0)
      (AVenhance.Infra.ODE.extendCurve P.htime y)) volume a b := by
  obtain ⟨C, hC, hb⟩ := P.projectedMatrix_bounded N v hv_bdd
  have hm : ∀ r c, AEStronglyMeasurable (fun t => P.projectedMatrix N v t r c) volume :=
    fun r c => (P.projectedMatrix_stronglyMeasurable N v hv_meas r c).aestronglyMeasurable
  exact plainMatrixODE_rhs_intervalIntegrable P.htime (P.projectedMatrix N v) (fun _ => 0)
    0 C hC hm hb intervalIntegrable_const y
end

/-! Component flux control retaining the weighted gradient energy. -/

section
open AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem flux_component_factorialRoot_le (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, TorusHk (k + 1) (h i)) (i : ι) :
    Real.sqrt (factorialNormSq ρ (P.flux t ht V i).val) ≤
      Real.sqrt (P.π i) * (ν * P.θ) *
        Real.sqrt (massGradNormSq ρ P.π (fun i => (V i).val)) := by
  have hc := componentFactorialRoot_le_mass ρ P.π P.hπ
    (fun i => (P.flux t ht V i).val) i
  have hf := Real.sqrt_le_sqrt (P.flux_mass_bound t ht V)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (mul_nonneg P.diffusivity_pos.le (P.theta_nonneg_of_component i))] at hf
  exact hc.trans ((mul_le_mul_of_nonneg_left hf (Real.sqrt_nonneg _)).trans_eq (by ring))

end TorusKernelOperator
end

/-! A single plain coefficient ODE supplies the Galerkin fields at all reserved orders. -/

section
open CoupledEnergy.Galerkin KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    {a b ρ ν : ℝ} {k l D : ℕ}

theorem kernelCoefficientRow_order
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
    (Q : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν l D)
    (hkl : k ≤ l) (hB : P.B = Q.B) (hC : P.C = Q.C) (hS : P.S = Q.S)
    (N : ℕ) (t : Set.Icc a b) (r : CoupledFourierModeIndex (h := h) N)
    (x : CoupledPlainCoefficients (h := h) N) :
    P.kernelCoefficientRow N t r x = Q.kernelCoefficientRow N t r x := by
  simp only [TorusKernelOperator.kernelCoefficientRow, TorusKernelOperator.fluxCoefficientRow,
    ContinuousLinearMap.comp_apply, neg_apply, sum_apply, ContinuousLinearMap.proj_apply,
    TorusKernelOperator.fluxCLM, TorusKernelOperator.fluxLinearMap,
    LinearMap.mkContinuous_apply, TorusKernelOperator.coefficientSynthesis]
  change -(∑ i, plainFluxForcingCLM N r i k
      (P.flux t t.property (fun i => coupledPlainSynthesis N i (k + 1) x) i)) =
    -(∑ i, plainFluxForcingCLM N r i l
      (Q.flux t t.property (fun i => coupledPlainSynthesis N i (l + 1) x) i))
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i _
  have hv : (fun i => truncateTorusHk (Nat.add_le_add_right hkl 1)
      (coupledPlainSynthesis N i (l + 1) x)) =
      (fun i => coupledPlainSynthesis N i (k + 1) x) := by
    funext i
    exact coupledPlainSynthesis_truncate (h := h) N i
      (K := k + 1) (L := l + 1) (Nat.add_le_add_right hkl 1) x
  have hf := kernelFlux_truncate P Q hkl hB hC hS t t.property
    (fun i => coupledPlainSynthesis N i (l + 1) x) i
  have hf' := hf.trans (congrArg
    (fun W : ∀ i, TorusHk (k + 1) (h i) => P.flux t t.property W i) hv)
  calc
    _ = plainFluxForcingCLM N r i k
        (truncateTorusHk hkl (Q.flux t t.property
          (fun i => coupledPlainSynthesis N i (l + 1) x) i)) :=
      congrArg (plainFluxForcingCLM N r i k) hf'.symm
    _ = _ := plainFluxForcing_truncate (h := h) N r i hkl _

theorem kernelMatrixEntry_order
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
    (Q : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν l D)
    (hkl : k ≤ l) (hB : P.B = Q.B) (hC : P.C = Q.C) (hS : P.S = Q.S)
    (N : ℕ) (t : Set.Icc a b) (r c : CoupledFourierModeIndex (h := h) N) :
    P.kernelMatrixEntry N t r c = Q.kernelMatrixEntry N t r c :=
  kernelCoefficientRow_order P Q hkl hB hC hS N t r (Pi.single c 1)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem noLocalCouplingIntegrand_eq_zero (N k : ℕ)
    (r c : CoupledFourierModeIndex (h := h) N) (t : ℝ) (x : Vec 2) :
    plainCouplingIntegrand N 0 (fun _ : ι => k)
      (fun i j d => TorusKernelOperator.noLocalCoefficient (h := h) (k := k) i j d t)
      r c x = 0 := by
  unfold plainCouplingIntegrand
  rw [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro d _
  exact (TorusKernelOperator.noLocalOrders i j d).elim

theorem projectedMatrix_order
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
    (Q : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν l D)
    (hkl : k ≤ l) (hB : P.B = Q.B) (hC : P.C = Q.C) (hS : P.S = Q.S)
    (N : ℕ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (r c : CoupledFourierModeIndex (h := h) N) :
    P.projectedMatrix N v t r c = Q.projectedMatrix N v t r c := by
  unfold TorusKernelOperator.projectedMatrix plainIntervalMatrix plainFourierMatrix
  simp only [noLocalCouplingIntegrand_eq_zero, add_zero]
  apply congrArg (fun z : ℝ => (∫ x in AVenhance.unitCube,
    plainDiffusionIntegrand N ν r c x +
      plainDriftIntegrand N (v (Set.projIcc a b P.htime t)) r c x) + z)
  exact kernelMatrixEntry_order P Q hkl hB hC hS N (Set.projIcc a b P.htime t) r c

theorem projectedMatrixCLM_order
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
    (Q : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν l D)
    (hkl : k ≤ l) (hB : P.B = Q.B) (hC : P.C = Q.C) (hS : P.S = Q.S)
    (N : ℕ) (v : ℝ → Vec 2 → Vec 2) :
    (fun t => plainMatrixCLM (P.projectedMatrix N v t)) =
      (fun t => plainMatrixCLM (Q.projectedMatrix N v t)) := by
  funext t
  apply congrArg plainMatrixCLM
  funext r c
  exact projectedMatrix_order P Q hkl hB hC hS N v t r c
end

/-! The complete diffusion and kernel flux retain the common gradient energy bound. -/

section
open AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Variational
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem total_flux_component_factorialRoot_le (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, TorusHk (k + 1) (h i)) (i : ι) :
    Real.sqrt (factorialNormSq ρ
      (ν • torusGradientTensor (V i) + P.flux t ht V i).val) ≤
      Real.sqrt (P.π i) * (ν * (1 + P.θ)) *
        Real.sqrt (massGradNormSq ρ P.π (fun i => (V i).val)) := by
  have hg := Real.sqrt_le_sqrt (componentGradFactorial_le_mass ρ P.π P.hπ
    (fun i => (V i).val) i)
  rw [Real.sqrt_mul (P.hπ i).le] at hg
  have hf := flux_component_factorialRoot_le P t ht V i
  have hs : AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (ν • (torusGradientTensor (V i)).val) =
      ν • AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (torusGradientTensor (V i)).val := by
    apply PiLp.ext
    intro j
    exact smul_comm (factorialRootWeight ρ j.1.val) ν ((torusGradientTensor (V i)).val j)
  have hadd := norm_add_le
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (ν • (torusGradientTensor (V i)).val))
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (P.flux t ht V i).val)
  rw [hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg P.diffusivity_pos.le,
    AVRegularity.CoupledEnergy.Variational.factorialWeightedJet_norm, torusGradientTensor_factorialNormSq,
    AVRegularity.CoupledEnergy.Variational.factorialWeightedJet_norm] at hadd
  change Real.sqrt (factorialNormSq ρ
    (ν • (torusGradientTensor (V i)).val + (P.flux t ht V i).val)) ≤ _
  rw [← AVRegularity.CoupledEnergy.Variational.factorialWeightedJet_norm, AVRegularity.CoupledEnergy.Variational.factorialWeightedJet_add, hs]
  calc
    _ ≤ ν * Real.sqrt (gradFactorialNormSq ρ (V i).val) +
        Real.sqrt (factorialNormSq ρ (P.flux t ht V i).val) := hadd
    _ ≤ ν * (Real.sqrt (P.π i) * Real.sqrt (massGradNormSq ρ P.π (fun i => (V i).val))) +
        Real.sqrt (P.π i) * (ν * P.θ) *
          Real.sqrt (massGradNormSq ρ P.π (fun i => (V i).val)) :=
      add_le_add (mul_le_mul_of_nonneg_left hg P.diffusivity_pos.le) hf
    _ = Real.sqrt (P.π i) * (ν * (1 + P.θ)) *
        Real.sqrt (massGradNormSq ρ P.π (fun i => (V i).val)) := by ring

end TorusKernelOperator
end

/-! The highest-order finite kernel equation is the same plain ODE at lower orders. -/

section
open CoupledEnergy.Galerkin KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    {a b ρ ν : ℝ} {k l D : ℕ}

theorem plainKernelZeroSource (N k : ℕ) :
    plainSourceCoefficients (h := h) N (fun _ => k) (fun _ => 0) (fun _ => 0) = 0 := by
  funext r
  simp only [plainSourceCoefficients, map_zero, sub_self, Finset.sum_const_zero, Pi.zero_apply]

theorem kernelODE_lower_order
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
    (Q : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν l D)
    (hkl : k ≤ l) (hB : P.B = Q.B) (hC : P.C = Q.C) (hS : P.S = Q.S)
    (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (initial : CoupledPlainCoefficients (h := h) N) (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (Q.projectedMatrix N v t)) (fun _ => 0) initial a b y) :
    AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun _ => plainSourceCoefficients N (fun _ => k) (fun _ => 0) (fun _ => 0)) initial a b y := by
  have hA := projectedMatrixCLM_order P Q hkl hB hC hS N v
  simpa only [hA, plainKernelZeroSource] using hy
end

/-! The incoming native stage's weighted dimensional flux is jointly measurable. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_weighted_dimFlux_joint_measurable
    {G : GenStage D hr Dm bw j₀} {M : ℕ} {k : InvConsts}
    (hnat : G.IsNatural M) (hcert : G.IsContextCertified k)
    (hΛ : 1 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (ν e E tS tZ mres : ℝ) (n : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn (G.innerDomain (Set.Icc tS tZ) mres) E n)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) :
    Measurable (fun z : Set.Icc tS tZ × (Vec 2 × Vec 2) =>
      G.fam.weight p z.1 • G.fam.dimFlux ν e E p (G.actual p) v u γ d I
        z.1 z.2.1 z.2.2) := by
  have hp : (G.fam.piece p).output = ocPulseWindow D.α D.q D.Λ G.level p.1 :=
    (hnat.1 p).2.1
  have hw : Measurable (G.fam.weight p) := by
    have he : G.fam.weight p = ocCutoff D.α D.q D.Λ G.level p.1 :=
      funext (hnat.2.1 p)
    rw [he]
    exact (CycleReference.ocCutoff_contDiff hΛ p.1).continuous.measurable
  apply weighted_dimFlux_joint_measurable_on_domain G.fam ν e E tS tZ n
    (G.innerDomain (Set.Icc tS tZ) mres) hs p (G.actual p) v u γ d I
    (fun t ht Y => G.innerDomain_native (Set.Icc tS tZ) mres p (hnat.2.2.1 p) hi hj t ht Y)
    (S := ocPulseWindow D.α D.q D.Λ G.level p.1)
  · exact measurableSet_Icc
  · exact hw
  · intro t ht
    apply G.fam.weight_zero p t
    rw [hp]
    exact ht
  · intro X z
    exact contextCertified_flux_time_measurable_vec hcert p (G.actual p) v u γ d I X z
end

/-! The order-zero physical flux inherits the component energy bound. -/

section
open AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Variational
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)

theorem total_flux_value_norm_le (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, TorusHk 1 (h i)) (i : ι) :
    ‖CoupledEnergy.Galerkin.torusHkValueCLM
      (ν • torusGradientTensor (V i) + P.flux t ht V i)‖ ≤
      Real.sqrt (P.π i) * (ν * (1 + P.θ)) *
        Real.sqrt (massGradNormSq ρ P.π (fun i => (V i).val)) := by
  let Q := ν • torusGradientTensor (V i) + P.flux t ht V i
  have hq : factorialNormSq ρ Q.val = ‖Q.val‖ ^ 2 := by
    rw [factorialNormSq_zero_eq_derivative, jet_norm_sq_eq_sum]
    simp
  have hb := total_flux_component_factorialRoot_le P t ht V i
  change Real.sqrt (factorialNormSq ρ Q.val) ≤ _ at hb
  rw [hq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
  exact (PiLp.norm_apply_le Q.val (valueIndex2 0)).trans hb

end TorusKernelOperator
end

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual OC velocity supplies the flow derivative budget on molecular time windows. -/

theorem actual_stream_spatial_derivative_bound
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 1 ≤ m)
    (t : ℝ) (x : Vec 2) :
    ‖Infra.Flow.jointSpatialFDeriv (streamVel (Φ m)) t x‖ ≤ 1048576 * ocA α q Λ m := by
  have he : 0 < ocEpsilon q Λ m := (Scales.epsilon_basic hq.1 hΛ).1
  have ha : 0 < ocA α q Λ m := Real.rpow_pos_of_pos he _
  have hfield := Infra.Construction.smoothPeriodic_streamVel
    (Velocity.streamSeq_admissible hζ hΛ hΦ m)
  have hb := Infra.Flow.jointSpatialFDeriv_bound_of_snorm hfield
    (mul_pos (mul_pos (by norm_num) ha) he) (mul_pos (by norm_num) (inv_pos.mpr he))
    (fun t => actual_stream_drift_snorm α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm t 1 le_rfl)
    t x
  exact hb.trans_eq (by field_simp; ring)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Family weights can be absorbed into the scalar input of the native operator. -/

open CycleJointProofs
variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem weighted_native_array_assembly
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ r : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (w : ℝ)
    (C : U →L[ℝ] V) (x : Vec 2) :
    nativeArrayAssembly r C
      (fun i A => transportedCoeff K Dγ (fun d I => w • B d I) r A x i) =
    w • nativeArrayAssembly r C
      (fun i A => transportedCoeff K Dγ B r A x i) := by
  have h : (fun i A => transportedCoeff K Dγ (fun d I => w • B d I) r A x i) =
      w • (fun i A => transportedCoeff K Dγ B r A x i) := by
    funext i A
    exact congrFun (transportedCoeff_smul_native K Dγ B w r A x) i
  rw [h, map_smul]

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! The incoming native constituent coefficients have the literal torus period. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_physCoeff_periodic
    {G : GenStage D hr Dm bw j₀} {M : ℕ}
    (hnat : G.IsNatural M) (hshift : G.IsShiftInvariant)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (t : ℝ) :
    IsZ2Periodic (G.physCoeff v u γ d t) := by
  have hT := GenStage.isTorusCompatible_of_shiftInvariant hnat hshift
  obtain ⟨N, hN⟩ := TorusCompatible.ocEpsilon_inv_natCast D.q D.Λ G.level
  exact hT.constituentPhysical_periodic (D.kap G.level) (D.eps G.level) hN v u γ d t

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Extract each component of the actual closed-time kernel identity. -/

open KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
theorem kernelFiniteTrace_pairing_to_trace (t : ℝ) (ht : t ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ B : ℝ, ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (F : ∀ i, ℝ → TorusHk (k) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (k) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, TorusHk (k) (h i))
    (N : ℕ → ℕ) (hN : StrictMono N)
    (y : (n : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) (N n)))
    (hy : ∀ n, AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun r => plainMatrixCLM (P.projectedMatrix (N n) v r))
      (fun r => plainSourceCoefficients (N n) (fun _ => k) (fun i => F i r) (fun i => g i r))
      (plainInitialCoefficients (N n) (fun _ => k) f) a b (AVenhance.Infra.ODE.extendCurve P.htime (y n)))
    (U : CoupledHighTime (h := h) (fun _ => k) a b) (Q : ℝ)
    (hu : ∀ n, ‖plainHigherBochner (N n) (fun _ => k) a b P.htime (y n)‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) (fun _ => k) a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainHigherBochner (N n) (fun _ => k) a b P.htime (y n))) atTop (𝓝 (ell U)))
    (i : ι) (φ : TorusHk 1 (h i))
    (u : TorusHk k (h i))
    (hid : inner ℝ (torusHkValueCLM u) (torusHkValueCLM φ) -
      inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
      P.kernelIntegratedRhs t v F g U i φ) :
    Tendsto (fun n => inner ℝ (torusHkValueCLM (coupledPlainSynthesis (N n) i k
      (AVenhance.Infra.ODE.extendCurve P.htime (y n) t))) (torusHkValueCLM φ)) atTop
      (𝓝 (inner ℝ (torusHkValueCLM u) (torusHkValueCLM φ))) := by
  have hp := P.kernelFiniteTrace_value_pairing_tendsto t ht v hv_bdd hv_meas hv F g hF hg
    f N hN y hy U Q hu hw i φ
  have he := (add_comm _ _).trans (eq_add_of_sub_eq hid).symm
  simpa only [he] using hp

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Copy-adapt the compiled closed trace while retaining its actual finite value sequence. -/

open KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernel_exists_weakTrace_with_value_sequence
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ (y : (N : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) N)) (n : ℕ → ℕ),
    ∃ (U : CoupledHighTime (h := h) (fun _ => k) a b) (u : ∀ i, ℝ → TorusHk (k) (h i)),
      (∀ i, MemLp (fun r => coupledHighGraphReadout (fun _ => k) i (U r)) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i, (coupledHighGraphReadout (fun _ => k) i (U r)).val = U r i) ∧
      (∀ i, u i a = f i) ∧
      (∃ R : ℝ, ∀ i, ∀ r ∈ Set.Icc a b, ‖u i r‖ ≤ R) ∧
      (∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
        inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
          inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
          P.kernelIntegratedRhs t v F g U i φ) ∧
      (∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
        (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b)) ∧
      (∀ i, MemLp (u i) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
        u i t = truncateTorusHk (Nat.le_succ (k)) (coupledHighGraphReadout (fun _ => k) i (U t))) ∧ StrictMono n ∧
      (∀ N, AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun t => plainMatrixCLM (P.projectedMatrix N v t))
        (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t))
        (plainInitialCoefficients N (fun _ => k) f) a b
        (AVenhance.Infra.ODE.extendCurve P.htime (y N))) ∧
      (∀ t ∈ Set.Icc a b, ∀ i, ∀ ψ : TorusHk 1 (h i),
        Filter.Tendsto (fun m => inner ℝ (torusHkValueCLM (coupledPlainSynthesis (n m) i k
          (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t))) (torusHkValueCLM ψ))
          Filter.atTop (𝓝 (inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM ψ)))) := by
  classical
  obtain ⟨y, U, n, hn, hy, hw, hmem, hgraphAE, hpoint⟩ :=
    P.kernelFourier_energy_closedTrace_subsequence v hv hvp F g αv B lam
      hα hB hlam hsmall hstrain hd hjets hv_bdd hv_meas f hF hg
  choose V ψ hψ hweak hgraph hinitial hnorm hid using (fun r : Set.Icc a b => hpoint r r.property)
  let u : ∀ i, ℝ → TorusHk (k) (h i) := fun i r =>
    if hr : r ∈ Set.Icc a b then ⟨V ⟨r, hr⟩ i, hgraph ⟨r, hr⟩ i⟩ else 0
  have huval (i : ι) (r : ℝ) (hr : r ∈ Set.Icc a b) : (u i r).val = V ⟨r, hr⟩ i := by
    simp only [u, dite_eq_left hr]
  have hidentity (i : ι) (r : ℝ) (hr : r ∈ Set.Icc a b) (φ : TorusHk 1 (h i)) :
      inner ℝ (torusHkValueCLM (u i r)) (torusHkValueCLM φ) -
        inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
        P.kernelIntegratedRhs r v F g U i φ := by
    have hi := hid ⟨r, hr⟩ i φ
    change inner ℝ ((u i r).val (valueIndex2 (k))) _ - _ = _
    rw [huval i r hr]
    exact hi
  have hcont : ∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
      (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b) := by
    intro i φ
    obtain ⟨Bv, hBv⟩ := hv_bdd
    have hc := P.kernelIntegratedRhs_continuousOn v hv_meas
      (fun r hr => (hv r hr).continuous) Bv hBv F g hF hg U i φ
    apply (hc.add continuousOn_const).congr
    intro r hr
    exact eq_add_of_sub_eq (hidentity i r hr φ)

  have hbound : ∃ R : ℝ, ∀ i, ∀ r ∈ Set.Icc a b, ‖u i r‖ ≤ R := by
    refine ⟨Real.sqrt ((∑ i, P.π i / factorialWeightMin ρ (k)) *
          (2 * massNormSq ρ P.π (fun i => (f i).val) +
            (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
            10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2)), ?_⟩
    intro i r hr
    change ‖(u i r).val‖ ≤ _
    rw [huval i r hr]
    exact (PiLp.norm_apply_le (V ⟨r, hr⟩) i).trans (hnorm ⟨r, hr⟩)
  let C : ℝ := 2 * massNormSq ρ P.π (fun i => (f i).val) +
    (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
    10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2
  let Qlo : ℝ := ∑ i, P.π i / factorialWeightMin ρ (k)
  let M : ℝ := ((∑ i, P.π i) * (b - a) + Qlo * (2 / ν)) * C
  have hQlo : 0 ≤ Qlo := Finset.sum_nonneg (fun i _ =>
    div_nonneg (P.hπ i).le (factorialWeightMin_pos ρ P.radius_pos (K := k)).le)
  have hhigh (m : ℕ) : ‖plainHigherBochner (n m) (fun _ => k) a b P.htime (y (n m))‖ ≤ Real.sqrt M := by
    have hs := (hy (n m)).2.2.2
    change _ ≤ M at hs
    simpa only [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hs
  have hfinite (m : ℕ) (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ‖torusHkValueCLM (coupledPlainSynthesis (n m) i (k)
        (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t))‖ ≤ Real.sqrt (Qlo * C) := by
    have he := (hy (n m)).2.2.1 t ht
    have hdiss : 0 ≤ (ν / 2) * (∫ s in Set.Icc a b,
        massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis (n m) i (k + 1)
          (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) s)).val)) :=
      mul_nonneg (div_nonneg P.diffusivity_pos.le (by norm_num))
        (integral_nonneg (fun s => massGradNormSq_nonneg ρ P.π P.hπ _))
    have hemass : massNormSq ρ P.π (fun i => (coupledPlainSynthesis (n m) i (k)
        (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t)).val) ≤ C := by
      change _ ≤ C at he
      linarith
    have hsq := (plainLowerSynthesis_normSq_le_mass (n m) (fun _ => k) ρ P.radius_pos P.π P.hπ
      (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t)).trans
      (mul_le_mul_of_nonneg_left hemass hQlo)
    have hl : ‖plainLowerSynthesisCLM (n m) (fun _ => k)
        (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t)‖ ≤ Real.sqrt (Qlo * C) := by
      simpa only [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hsq
    exact (PiLp.norm_apply_le
      (coupledPlainSynthesis (n m) i (k) (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t)).val
      (valueIndex2 (k))).trans ((PiLp.norm_apply_le
        (plainLowerSynthesisCLM (n m) (fun _ => k) (AVenhance.Infra.ODE.extendCurve P.htime (y (n m)) t)) i).trans hl)
  have halign : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      u i t = truncateTorusHk (Nat.le_succ (k)) (coupledHighGraphReadout (fun _ => k) i (U t)) := by
    apply plainTrace_eq_highGraph_ae (fun _ => k) a b U u hgraphAE
    intro cutoff
    apply ae_all_iff.mpr
    intro r
    exact P.kernelEquation_trace_pairing_eq_ae v hv_bdd hv_meas
      (fun t ht => (hv t ht).continuous) F g hF hg f n hn
      (fun m => y (n m)) (fun m => (hy (n m)).1) U (Real.sqrt M) hhigh hw
      r.1 (coupledModeHk cutoff r r.1 1) _ (hcont r.1 _) (Real.sqrt (Qlo * C))
      (fun m t ht => hfinite m r.1 t ht) (fun t ht => hidentity r.1 t ht _)
  obtain ⟨R, hR⟩ := hbound
  refine ⟨y, n, U, u, hmem, hgraphAE, ?_, ⟨R, hR⟩, hidentity, hcont, ?_, halign, hn, fun N => (hy N).1, ?_⟩
  · intro i
    apply Subtype.ext
    rw [huval i a ⟨le_rfl, P.htime⟩, hinitial ⟨a, ⟨le_rfl, P.htime⟩⟩ rfl]
  · exact fun i => plainTrace_memLp (fun _ => k) a b u hcont R hR i

  · intro t ht i ψ
    exact kernelFiniteTrace_pairing_to_trace P t ht v hv_bdd hv_meas
      (fun r hr => (hv r hr).continuous) F g hF hg f n hn
      (fun m => y (n m)) (fun m => (hy (n m)).1) U (Real.sqrt M) hhigh hw i ψ
      (u i t) (hidentity i t ht ψ)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Time integrability of the actual complete order-zero physical flux. -/

open AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Variational
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)

theorem total_flux_value_memLp (w : ∀ i, ℝ → TorusHk 1 (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    MemLp (fun t => CoupledEnergy.Galerkin.torusHkValueCLM
      (ν • torusGradientTensor (w i t) + P.carrierFlux w i t))
      2 (volume.restrict (Set.Icc a b)) := by
  have hg := torusGradientTensor_carrier_memLp 0 a b (w i) (hw i)
  have hs := (hg.const_smul ν).add (P.carrierFlux_memLp_of_family w hw i)
  simpa only [Function.comp_def] using!
    (CoupledEnergy.Galerkin.torusHkValueCLM (E := PiLp 2 (fun _ : Fin 2 => h i))).comp_memLp' hs

end TorusKernelOperator

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory MeasureTheory.Lp Homogenization Set
open AVenhance.Infra.Parabolic.WeakUniqueness
namespace AVRegularity.Construction.Preservation.Buffer

/-! Copy-adapt compact strong-time calculus to arbitrary smooth fields on the finite cell. -/

theorem smooth_scalar_cell_strong_time {a b : ℝ} (hab : a ≤ b)
    (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (z dz : ℝ → Lp ℝ 2 (volume.restrict AVenhance.unitCube))
    (hz : ∀ t, z t =ᵐ[volume.restrict AVenhance.unitCube] fun x => f (t, x))
    (hdz : ∀ t, dz t =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => fderiv ℝ f (t, x) (1, 0)) :
    CycleEvolution.StrongTimeRegularity a b z dz := by
  let K := Icc (a - 1) (b + 1) ×ˢ WeakAlgebra.weakSpatialClosedCell
  have hK : IsCompact K := isCompact_Icc.prod WeakAlgebra.weakSpatialClosedCell_compact
  obtain ⟨g, hg, hcg, heq⟩ := exists_compact_smooth_localization K hK f hf
  obtain ⟨u, du, hu, hdu, ht⟩ :=
    CycleJointProofs.compactScalar_l2_strong_time g (hg.of_le (by simp)) hcg a b
  have hm : volume.restrict AVenhance.unitCube ≤ (1 : ENNReal) • volume := by
    rw [one_smul]
    exact Measure.restrict_le_self
  let L : Lp ℝ 2 (volume : Measure (Vec 2)) →L[ℝ]
      Lp ℝ 2 (volume.restrict AVenhance.unitCube) :=
    LpToLpOfMeasureLeSMul (by simp : (1 : ENNReal) ≠ ⊤) hm
  have hv : EqOn (fun t => L (u t)) z (Ioo (a - 1) (b + 1)) := by
    intro t hti
    apply Lp.ext
    filter_upwards [coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ENNReal) ≠ ⊤) hm (u t),
      (hu t).filter_mono (ae_mono Measure.restrict_le_self), hz t,
      ae_restrict_mem AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge.bridge_unitCube_measurable]
      with x hL hx hzv hxc
    have hp : (t, x) ∈ K := ⟨⟨hti.1.le, hti.2.le⟩,
      WeakAlgebra.weakUnitCube_subset_closedCell hxc⟩
    exact hL.trans (hx.trans ((heq (t, x) hp).eq_of_nhds.trans hzv.symm))
  have hdv : EqOn (fun t => L (du t)) dz (Icc a b) := by
    intro t hti
    apply Lp.ext
    filter_upwards [coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ENNReal) ≠ ⊤) hm (du t),
      (hdu t).filter_mono (ae_mono Measure.restrict_le_self), hdz t,
      ae_restrict_mem AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge.bridge_unitCube_measurable]
      with x hL hx hzv hxc
    have hp : (t, x) ∈ K := ⟨⟨by linarith [hti.1], by linarith [hti.2]⟩,
      WeakAlgebra.weakUnitCube_subset_closedCell hxc⟩
    have hd : fderiv ℝ g (t, x) = fderiv ℝ f (t, x) := (heq (t, x) hp).fderiv_eq
    exact hL.trans (hx.trans ((congrArg (fun A => A (1, 0)) hd).trans hzv.symm))
  exact strong_time_window_congruence hab (ht.map L) hv hdv

end AVRegularity.Construction.Preservation.Buffer
end
end
