-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
public import AVRegularity.Construction.Preservation.CommonPreparation.NativeBufferedSlotDatum
import AVRegularity.Construction.Preservation.Assembly.PreparationJointOfInputs
import AVRegularity.EntryTerminal.Ingredients.PrepChart.Chart
import AVRegularity.Construction.EntryScales.TerminalCore
public import AVRegularity.Construction.KernelDefect.UniformDefect
import AVRegularity.CycleComparison.Reconstruction.PiolaTested
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.CycleComparison.Error.WeakSolution
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledEnergyTorus
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Uniform production of the original-stage preparation kernel tower.
The highest-order certificate price is chosen before OCData and stages and
absorbed by the incoming marked ledger at a late level. Every actual kernel
is used unchanged, and its order-zero regularizer supplies all finite orders.
Seed and descendant stages use exactly the same original-stage argument.
No high-order invariant premise or bound K<=Ks is introduced. -/

open FullLift RetainedEnergy

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The source package uses only clauses already carried by the seed
and incoming stage, for both the seed itself and its cascade descendants. -/
theorem preparation_source_of_generated_seed (F : Request hr D Dm bw j₀)
    (kS k : InvConsts) (Mnat n r₀ D₀ : ℕ) (tS tA Ce τe S θ : ℝ)
    (seed : GenStage D hr Dm bw j₀) (Mn : SuccMenu)
    (Cw cr σ₀ η₀ : ℝ) (N p : ℕ)
    (hP : F.P = succProvParams D Cw cr σ₀ η₀ N p) (hcr : cr ≤ 1)
    (hseed : IsGeneratedSeed F.law F.P F.seedK F.freshK F.φ₀ F.hφ₀ Mnat kS seed n tS F.tf Ce τe r₀ D₀)
    (hterm : seed.level ≤ D.term) (hc : IsCascadeStage D F.P Mn seed F.G)
    (hprod : k.Hprod = k.G0 + Mn.H + 1) (hradius : F.c₀ = k.c₀)
    (hI : IsStageInvariant F.law F.P F.seedK F.freshK F.φ₀ F.hφ₀ Mnat k tA F.tf S θ F.G) :
    Nonempty (PreparationNativeSource F k Mnat tA S θ) := by
  have hseedI := hseed.2.2.2.2.2.2.2.1
  refine ⟨{
    seed := seed
    menu := Mn
    Cw := Cw
    cr := cr
    σ₀ := σ₀
    η₀ := η₀
    N := N
    p := p
    parameters := hP
    cr_le_one := hcr
    seed_empty := hseed.2.1
    seed_tags := hseedI.2.1
    seed_lengths := ?_
    seed_terminal := hterm
    cascade := hc
    product := hprod
    radius := hradius
    invariant := hI }⟩
  intro v u γ hb
  simpa only [hseed.1] using (hseed.2.2.2.2.2.1 v u γ).2.2 hb

/-- Highest-order native production, uniformly before the actual stage and datum.
The larger regularizer constants CK are fixed before selecting the source family. -/
theorem preparation_top_operators (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : PreparationNativeStatement true α q ζ := by
  classical
  obtain ⟨Λ₀, hΛ₀, hlength⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ bw hbw K Dm hDm CK hCK
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  obtain ⟨A, hA, mo, hmo, hop⟩ := uniform_native_kernel_operator_of_certificates
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ h128 ζ hζ bw hbw K Dm hDm CK hCK
  refine ⟨A, hA, fun CI τ c₀ hτ hc₀ hc₀le j₀ => ?_⟩
  obtain ⟨ma, habs⟩ := retained_absorption_threshold hq.1 h128 hτ A CI
  let mStar := max (mo + 1) (max j₀ (max 2 ma))
  refine ⟨mStar, (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)), ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq M hband hterm F hc hm hmM k Mnat tA θ src
    htA htf hcker
  have hmoG : mo + 1 ≤ F.G.level := (le_max_left _ _).trans hm
  have hj : j₀ ≤ F.G.level := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hi : 1 ≤ F.G.level := by
    have h2 := (le_max_left 2 ma).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
    omega
  have hma : ma ≤ F.G.level + 1 := by
    have h := (le_max_right 2 ma).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
    omega
  have hΛD : 128 ≤ D.Λ := hDΛ ▸ h128
  have hqD : 1 < D.q := hDq ▸ hq.1
  have hζD : IsFastProfile D.ζ := hDζ ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have he (l : ℕ) : 0 < D.eps l := Construction.Stream.ocEpsilon_pos (by omega)
  have hκ : 0 < D.κ F.G.level :=
    CycleReference.bandChain_pos (by omega) hζD hbandD (hterm.symm ▸ hmM)
  have hkap : D.kap F.G.level = D.κ F.G.level := by
    change D.κ (min F.G.level D.term) = _
    rw [Nat.min_eq_left (hterm.symm ▸ hmM)]
  have ha : 0 < ocA D.α D.q D.Λ F.G.level := Real.rpow_pos_of_pos (he F.G.level) _
  have hradius := Buffer.molecular_radius_bounds (hc ▸ hc₀) (he F.G.level) hκ ha
  have hρ : 0 < rhoStar D F.c₀ F.G.level := hradius.1
  have hρe : rhoStar D F.c₀ F.G.level ≤ D.eps F.G.level :=
    hradius.2.1.trans (mul_le_of_le_one_left (he F.G.level).le (hc ▸ hc₀le))
  have hρE : rhoStar D F.c₀ F.G.level ≤ D.eps (F.G.level - 1) :=
    hρe.trans (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hlens := hlength hr D hDα hDq hDζ (by rw [hDΛ]; exact hΛ) hbandD Dm bw j₀
    src.menu src.Cw src.cr src.σ₀ src.η₀ src.N src.p src.cr_le_one src.seed F.G
    (by rw [← src.parameters]; exact src.seed_tags) src.seed_lengths src.seed_terminal
    (by rw [← src.parameters]; exact src.cascade) hi
  have hlen : ∀ v u (γ : F.G.fam.Γ v u), 3 ≤ (F.G.fam.identity v u γ).maxOrder →
      (F.G.fam.identity v u γ).record.length ≤ D.eps (F.G.level - 1) := by
    intro v u γ hd
    have hb : 1 ≤ (F.G.fam.identity v u γ).record.birthExcess := by
      have hh := (F.G.fam.identity v u γ).le_birth
      omega
    exact (hlens v u γ hb).trans
      (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hmreserve (v : CompIn F.G.comps) : 0 ≤ compReserve k v.1 :=
    (Buffer.cascade_component_reserve_pos src.seed_empty src.cascade k src.product v).le
  have hmreserve2 (v : CompIn F.G.comps) : compReserve k v.1 ≤ 2 :=
    (Buffer.compReserve_le_one k v.1).trans (by norm_num)
  obtain ⟨hnat, _htags, _hgen, hshift, hpar, hcert, _henv, hledger, hkernel, _hrest⟩ := src.invariant
  have hwidth : ∀ v u γ, (F.G.kernelOf F.P F.seedK F.freshK v u γ).width =
      (F.G.fam.identity v u γ).record.width := fun v u γ => (hkernel v u γ).2.1
  have hwpos (v u : CompIn F.G.comps) (γ : F.G.fam.Γ v u) :
      0 < (F.G.kernelOf F.P F.seedK F.freshK v u γ).width := by
    rw [hwidth]
    exact (F.G.fam.identity v u γ).record.width_pos
  have hsub : Set.Icc F.s F.tf ⊆ Set.Icc tA F.tf := fun t ht => ⟨htA.trans ht.1, ht.2⟩
  have hSzero : ∀ v u γ, IsSpatialRegularizerTorus (rhoStar D F.c₀ F.G.level) 0 Dm F.s F.tf CK
      (F.G.kernelOf F.P F.seedK F.freshK v u γ).width
      (F.G.sysS F.P F.seedK F.freshK F.φ₀ F.hφ₀ v u γ) := by
    intro v u γ
    have hs := Buffer.spatialRegularizerTorus_time_restrict
      ((hkernel v u γ).2.2.2.2 _ hρ 0 (Nat.zero_le _)) hsub
    exact spatial_regularizer_constants_mono hs (hwpos v u γ).le hcker
  have hsmall : A * (CI * D.eps F.G.level ^ τ) ≤ 1 / 8 := by
    have h := habs (F.G.level + 1) hma
    simpa only [Nat.add_sub_cancel, OCData.eps, hDq, hDΛ] using h.le
  have hop' := hop hr D hDα hDq hDΛ hDζ hseq j₀ Mnat F.G k hcert hnat hshift hmoG hi hj
    (he _) (he _) (hkap.symm ▸ hκ) hpar hmreserve hmreserve2
    F.P F.seedK F.freshK hwidth F.φ₀ F.hφ₀ F.s F.tf (rhoStar D F.c₀ F.G.level)
    (CI * D.eps F.G.level ^ τ) (F.G.mass F.law) (F.G.marker F.law)
    htf hρ hρE hρe hlen
    (fun v => Buffer.birth_compMass_pos hqD hΛD F.law v.1)
    (fun v => Buffer.birth_compMarker_pos hqD hΛD F.law v.1) hledger hsmall hSzero
  rw [hkap] at hop'
  let R := fun w hw => Classical.choose (hop' w hw)
  have hR := fun w hw => Classical.choose_spec (hop' w hw)
  refine ⟨{
    operators := R
    coefficient := fun w hw => (hR w hw).1
    inclusion := fun w hw => (hR w hw).2.1
    kernel := fun w hw => (hR w hw).2.2.1
    mass := fun w hw => (hR w hw).2.2.2.1
    width := fun w hw => (hR w hw).2.2.2.2.1
    constants := fun w hw => (hR w hw).2.2.2.2.2.1
    price := fun w hw => (hR w hw).2.2.2.2.2.2
    width_positive := hwpos
    regularizer := hSzero }⟩

/-- The original-stage finite tower, with its sole production ingredient discharged. -/
theorem preparation_native_operators (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : PreparationNativeStatement false α q ζ :=
  preparation_native_statement_of_top (preparation_top_operators α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization AVenhance Filter
open scoped Topology
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual native stream has every finite-order drift package at one
order-independent molecular cap. The uniform memory-scale bound also puts
the molecular buffer delay below two renewal times, before any band chain,
stream, observation window or datum is chosen. -/

open CycleReference Buffer

/-- The shared molecular cap supplies the actual all-order native drift and
its two-renewal delay at every sufficiently late interior stage. -/
theorem native_preparation_drift {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    NativePreparationDriftStatement α q ζ := by
  obtain ⟨Cm, _, Λ₀, hΛ₀, hmemory⟩ :=
    bandChain_memory_scale hα₀ hα₁ hs₀ hs₁ hq hζ
  have hcap := exists_molecular_uniform_constants.choose_spec
  refine ⟨Λ₀, hΛ₀, exists_molecular_uniform_constants.choose, hcap.1, le_rfl, ?_⟩
  intro Λ hΛ c₀ hc₀ hccap
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hlim : Tendsto (fun m : ℕ => Cm * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (preparation_parent_power_tendsto_zero hq.1 h128
        (mul_pos (by norm_num : (0 : ℝ) < 4) hδ))
  obtain ⟨mc, hmc⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_le_nhds zero_lt_one))
  refine ⟨max 2 mc, le_max_left _ _, ?_⟩
  intro M κ hband m hm hmM Φ hΦ
  have hm2 : 2 ≤ m := by omega
  have he : 0 < ocEpsilon q Λ m := Stream.ocEpsilon_pos hΛ1
  have hν : 0 < κ m := bandChain_pos hΛ1 hζ hband hmM.le
  have ha : 0 < ocA α q Λ m := Real.rpow_pos_of_pos he _
  have hτ : 0 < ocTau α q Λ m := Stream.ocTau_pos hΛ1
  have hτPP : 0 < ocTauPP α q Λ m := Stream.ocTauPP_pos hΛ1
  have hcdata := hcap.2 c₀ hc₀ hccap
  have hd := hcdata.2.2 (ocEpsilon q Λ m) (κ m) (ocA α q Λ m) he hν ha
  let ρ := c₀ * min (ocEpsilon q Λ m) (Real.sqrt (κ m / ocA α q Λ m))
  have hρ : 0 < ρ := hd.1
  have hρε : ρ ≤ ocEpsilon q Λ m :=
    hd.2.1.trans ((mul_le_mul_of_nonneg_right hcdata.1 he.le).trans_eq (one_mul _))
  have hmem := (hmemory Λ hΛ M (by omega) κ hband m hm2 hmM.le).1
  rw [ocEll_sq_eq hν] at hmem
  have hcell : ocEpsilon q Λ m ^ 2 / κ m ≤ ocTau α q Λ m :=
    (div_le_one hτ).mp (hmem.trans (hmc m (by omega)))
  have hL : (1 : ℝ) ≤ (ocL α q Λ m : ℝ) := by
    exact_mod_cast (show 1 ≤ ocL α q Λ m by unfold ocL; omega)
  have htime : ocTau α q Λ m ≤ ocTauPP α q Λ m :=
    div_le_self hτPP.le (one_le_pow₀ hL)
  refine ⟨?_, ?_⟩
  · calc
      ρ ^ 2 / κ m ≤ ocEpsilon q Λ m ^ 2 / κ m :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hρ.le hρε 2) hν.le
      _ ≤ ocTau α q Λ m := hcell
      _ ≤ ocTauPP α q Λ m := htime
      _ ≤ 2 * ocTauPP α q Λ m := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hτPP.le
  · intro a b Kmax
    obtain ⟨hsm, hper, hdiv, hbdd, hmeas⟩ :=
      stream_kernel_drift_data (Velocity.streamSeq_admissible hζ h128 hΦ m) a b
    refine ⟨hbdd, hmeas, hsm, hdiv, hper, actualDriftJetConstant * ocA α q Λ m,
      1024, ocEpsilon q Λ m, mul_nonneg actualDriftJetConstant_nonneg ha.le,
      by norm_num, he, ?_, hd.2.2.1, hd.2.2.2.1⟩
    intro l hl _ t _ x
    exact actual_stream_drift_arrays α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ h128
      Φ hΦ m (by omega) t l hl x

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! One linear evolution for a genuine descending preparation family. The
frame records exactly the inputs of the triangular torus solver;
uniqueness, addition and real scaling make its trace linear before the datum
is selected. No small Schur bound or additional PDE existence is required.

Empty and singleton families, depth zero, zero data, edgeless seeds and degenerate windows
are allowed. The
trace is clamped only outside its solution window. All higher lifts and
spatial integrability at every time remain part of the actual equation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Part : Type*} {Ctx : Part → Type*}

local instance preparationPlainNativeModule (k : ℕ) (i : ι) :
    Module ℝ (TorusHk k (h i)) := inferInstance
local instance preparationPlainCarrierSMul (k : ℕ) (i : ι) : SMul ℝ (TorusHk k (h i)) :=
  (preparationPlainNativeModule (h := h) k i).toDistribMulAction.toDistribSMul.toSMul
local instance preparationPlainFamilySMul (K : ι → ℕ) :
    SMul ℝ (∀ i, TorusHk (K i) (h i)) := Pi.instSMul

/-- The precise environment already used by actual preparation existence and
uniqueness, bundled once for the plain-layer construction. -/
structure PreparationPlainFrame (family : ChartedFamily ι h D Part Ctx) where
  K : ι → ℕ
  Kmax : ℕ
  H : ℕ
  order_bound : ∀ i, K i ≤ Kmax
  depth : family.HasDepthAtMost H
  ρ : ℝ
  ν : ℝ
  a : ℝ
  b : ℝ
  radius_pos : 0 < ρ
  diffusivity_pos : 0 < ν
  time_order : a ≤ b
  α : ℝ
  q : ℝ
  Λ : ℕ
  m : ℕ
  Φ : ℕ → ℝ → Vec 2 → ℝ
  ζ : ℝ → ℝ
  fast_profile : IsFastProfile ζ
  stream_sequence : IsOCStreamSeq α q Λ ζ Φ
  φ : ℝ → Vec 2 → ℝ
  admissible_stream : IsAdmissibleStream φ
  Cpad : ℝ
  Cage : ℝ
  Npad : ℕ
  Jchart : ℕ
  Cchart : ℕ → ℝ
  l₀ : ℤ
  P : ℕ
  preparation : IsPreparationChartCertificate α q Λ m φ admissible_stream
    a b Cpad Cage Npad Jchart Cchart l₀ P family
  e : ℝ
  E : ℝ
  actual : ∀ p, Ctx p
  measurable : family.IsTimeMeasurable
  weight_measurable : ∀ p, Measurable (family.weight p)
  coarse_scale : E = ocEpsilon q Λ (m - 1)
  radius_scale : ρ ≤ e
  scale_order : e ≤ E
  Jm : ℕ
  chart_order : Kmax + D + 2 ≤ Jchart
  molecular_order : Kmax + D + 2 ≤ Jm
  Cm : ℕ → ℝ
  π : ι → ℝ
  mass_pos : ∀ i, 0 < π i
  A : ι → ι → ℝ
  majorant_nonneg : ∀ i j, 0 ≤ A i j
  fine_scale : e = ocEpsilon q Λ m
  torus : IsTorusCompatible family actual E
  pointwise : IsPointwiseMolecularEnvelope family π K
    (ChartedFamily.Domain.onWindow family (Set.Icc a b)) ν e E ρ Cm Jm
    (fun v u => Real.sqrt (π u / π v) * A v u)

variable {family : ChartedFamily ι h D Part Ctx}

/-- Put the entire buffered datum in copy zero; only added copies have zero
initial trace. The dependent slots are preserved by the Pi single map. -/
def preparationNeutralInitial (H : ℕ) (K : ι × Fin (H + 1) → ℕ) :
    (∀ i, TorusHk (K (i, 0)) (h i)) →ₗ[ℝ]
      (∀ v : ι × Fin (H + 1), TorusHk (K v) (h v.1)) :=
  LinearMap.pi fun v =>
    ((LinearMap.proj v.1).comp (LinearMap.proj v.2)).comp (LinearMap.single ℝ
      (fun l : Fin (H + 1) => ∀ i, TorusHk (K (i, l)) (h i)) 0)

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The original copy keeps the full higher buffered trace. -/
theorem preparation_neutral_initial_zero_copy (H : ℕ) (K : ι × Fin (H + 1) → ℕ)
    (f : ∀ i, TorusHk (K (i, 0)) (h i)) (i : ι) :
    preparationNeutralInitial H K f (i, 0) = f i := by
  change ((Pi.single (0 : Fin (H + 1)) f :
    ∀ l : Fin (H + 1), ∀ i, TorusHk (K (i, l)) (h i)) 0) i = f i
  rw [Pi.single_eq_same]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- New copies alone have zero initial trace. -/
theorem preparation_neutral_initial_positive_copy (H : ℕ) (K : ι × Fin (H + 1) → ℕ)
    (f : ∀ i, TorusHk (K (i, 0)) (h i)) (v : ι × Fin (H + 1)) (hv : v.2 ≠ 0) :
    preparationNeutralInitial H K f v = 0 := by
  change ((Pi.single (0 : Fin (H + 1)) f :
    ∀ l : Fin (H + 1), ∀ i, TorusHk (K (i, l)) (h i)) v.2) v.1 = 0
  rw [Pi.single_eq_of_ne hv]
  rfl

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Native preparation chart certificates on arbitrary short subwindows.
Constants remain uniform in the start and duration; in particular the last
piece of a long observation window may be shorter than two renewal periods.
The degenerate cases are included: a point window, empty and singleton fibres, identity geometry and
an edgeless seed use the same native charts. No whole-window age bound is used. -/

/-- The native schedule and flow producer supplies certificates
on every interval of length at most two renewal periods, at all finite orders. -/
def NativeShortChartCertificateStatement (α q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∀ Λ : ℕ, 128 ≤ Λ →
  ∃ (Cpad Cage : ℝ) (Npad : ℕ) (Cchart : ℕ → ℝ) (mStar : ℕ),
    0 ≤ Cpad ∧ 0 < Cage ∧ 2 ≤ mStar ∧
  ∀ (data : OCData), data.α = α → data.q = q → data.Λ = Λ →
    IsOCStreamSeq α q Λ ζ data.Φ →
  ∀ (Mnat m : ℕ), mStar ≤ m → m ≤ Mnat →
  ∀ {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {Ctx : OddSlot → Type*} (F : ChartedFamily ι h D OddSlot Ctx),
    (∀ pc, IsNaturalPiece data Mnat m pc.val (F.piece pc)) →
  ∀ (a b : ℝ) (Jchart : ℕ), a ≤ b → b - a ≤ 2 * ocTauPP α q Λ m →
    ∃ (l₀ : ℤ) (P : ℕ),
      IsPreparationChartCertificate α q Λ m (data.Φ (m - 1)) (data.hΦ (m - 1))
        a b Cpad Cage Npad Jchart Cchart l₀ P F

/-! Native preparation certificates on shorter intervals. Restriction retains
the original reference chart and schedule; enlarging the padding by two periods
contains the full availability geometry. The existing flow producer supplies
the same native flow's all-order bounds on this enlarged padded interval. -/

private theorem short_padded_window_subset {a b T C : ℝ}
    (hT : 0 ≤ T) (hab : a ≤ b) :
    preparationPaddedWindow a (a + 2 * T) C T ⊆
      preparationPaddedWindow a b (C + 2) T := by
  intro t ht
  change a - (C + 2) * T ≤ t ∧ t ≤ b + (C + 2) * T
  change a - C * T ≤ t ∧ t ≤ a + 2 * T + C * T at ht
  constructor <;> linarith only [ht.1, ht.2, hT, hab]

/-- The full native preparation certificate restricts to every interval
of at most two renewal periods, uniformly in its duration and finite order. -/
theorem nativeShortChartCertificate {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    NativeShortChartCertificateStatement α q ζ := by
  intro Λ hΛ
  obtain ⟨Cpad, Cage, Npad, _, hpad, hage, ms, hms, hfull⟩ :=
    Assembly.preservation_preparation_chart_certificate α s q hα₀ hα₁ hs₀ hs₁
      hq ζ hζ Λ hΛ
  obtain ⟨C, _, hflow⟩ := EntryTerminal.Ingredients.prep_flow_jets
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨mf, _, hflow⟩ := hflow Λ hΛ Cage hage
  refine ⟨Cpad + 2, Cage, Npad, EntryTerminal.Ingredients.prepChartConst C,
    max ms mf, by linarith only [hpad], hage, hms.trans (le_max_left _ _), ?_⟩
  intro data hDα hDq hDΛ hΦ Mnat m hm hmM ι h _ _ D Ctx F hnat a b Jchart hab hlen
  have hm2 : 2 ≤ m := hms.trans ((le_max_left _ _).trans hm)
  have hh : 0 < ocTauPP α q Λ m := Construction.Stream.ocTauPP_pos (by omega : 1 ≤ Λ)
  let l₀ : ℤ := ⌊a / ocTauPP α q Λ m + 1 / 2⌋
  have hf := Int.floor_le (a / ocTauPP α q Λ m + 1 / 2)
  have hf' := Int.lt_floor_add_one (a / ocTauPP α q Λ m + 1 / 2)
  have hleft : ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ a := by
    apply (le_div_iff₀ hh).mp
    change (l₀ : ℝ) ≤ a / ocTauPP α q Λ m + 1 / 2 at hf
    linarith only [hf]
  have hright : a < ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m := by
    apply (div_lt_iff₀ hh).mp
    change a / ocTauPP α q Λ m + 1 / 2 < (l₀ : ℝ) + 1 at hf'
    linarith only [hf']
  have hend : a + 2 * ocTauPP α q Λ m ≤
      ((l₀ : ℝ) + (3 : ℕ) - 1 / 2) * ocTauPP α q Λ m := by
    norm_num only [Nat.cast_ofNat]
    linarith only [hright]
  have hsch := (hfull data hDα hDq hDΛ Mnat m hm2 ((le_max_left _ _).trans hm)
    hmM a l₀ 3 (by norm_num) hleft hright hend F hnat hΦ Jchart).schedule
  have hsub : Set.Icc a b ⊆ Set.Icc a (a + 2 * ocTauPP α q Λ m) := by
    intro t ht
    exact ⟨ht.1, ht.2.trans (by linarith only [hlen])⟩
  have hmeet (p : OddSlot) (hp : ((F.piece p).output ∩ Set.Icc a b).Nonempty) :
      ((F.piece p).output ∩ Set.Icc a (a + 2 * ocTauPP α q Λ m)).Nonempty :=
    hp.mono (Set.inter_subset_inter_right _ hsub)
  have hpadsub := short_padded_window_subset (C := Cpad) hh.le hab
  refine ⟨l₀, 3, ?_, hflow data.Φ hΦ m ((le_max_right _ _).trans hm)
    (data.hΦ (m - 1)) a b (Cpad + 2) Jchart⟩
  exact
    { pad_nonneg := by linarith only [hpad]
      age_pos := hage
      finite_pieces := hsch.finite_pieces.subset (fun p hp => hmeet p hp)
      reference_mem := hpadsub hsch.reference_mem
      availability_interval := fun p hp => hsch.availability_interval p (hmeet p hp)
      anchor_label := fun p hp => hsch.anchor_label p (hmeet p hp)
      natural := fun p hp => hsch.natural p (hmeet p hp)
      geometry_padded := fun p hp => (hsch.geometry_padded p (hmeet p hp)).trans hpadsub
      anchor_age := fun p hp => hsch.anchor_age p (hmeet p hp)
      reference_age := fun p hp => hsch.reference_age p (hmeet p hp)
      anchor_segments := fun p hp => hsch.anchor_segments p (hmeet p hp)
      reference_segments := fun p hp r hr =>
        (hsch.reference_segments p (hmeet p hp) r hr).trans hpadsub
      cover_labels := fun p hp => hsch.cover_labels p (hmeet p hp)
      core_label := fun p t ht => hsch.core_label p t ⟨ht.1, hsub ht.2⟩ }

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Whole-window energy for the SAME actual forward-copy solution at its
original masses, without a whole-window chart. This is the quantitative
adapter needed in the finite insertion price; it uses the coupled
energy estimate `coupled_energy_torus` and rank-mass conversion, not a new evolution.
The degenerate cases are included: H=0 or D=2, empty and singleton components, identity geometry,
zero coefficients, constants, and point windows retain the factor 2. S=0 is
allowed; no norm or integral is divided out. -/

/-- Rank inflation prices the actual copy solution at any common Schur
row/column bound S, uniformly in its datum and observation window. -/
def RawCopiedPlainEnergyStatement : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (H D Kmax : ℕ) (K : ι × Fin (H + 1) → ℕ), 2 ≤ D → (∀ v, K v ≤ Kmax) →
  ∀ (ν ρ a b : ℝ) (v : ℝ → Vec 2 → Vec 2), 0 < ν → 0 < ρ → a ≤ b →
    Providers.WeakGen.Comparison.TorusDriftData ν ρ a b v Kmax →
  ∀ (π : ι → ℝ), (∀ i, 0 < π i) →
  ∀ A : ∀ x y : ι × Fin (H + 1), (d : admissibleOrders K D x y) → ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h y.1)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h x.1)),
    (∀ x y d, coefficientSeminorm ρ (K x) a b (A x y d) ≠ ⊤) →
    (∀ x y d, Measurable (fun p : Set.Icc a b × Vec 2 => A x y d p.1 p.2)) →
    (∀ x y d t, t ∈ Set.Icc a b → ContDiff ℝ (K x : ℕ) (A x y d t)) →
    (∀ x y d t, t ∈ Set.Icc a b → IsZ2Periodic (A x y d t)) →
    (∀ x y d, x.2.val ≠ y.2.val + 1 → ∀ t ∈ Set.Icc a b, A x y d t = 0) →
  ∀ S : ℝ, 0 ≤ S →
    SchurBound S (schurMatrix ν ρ (fun x => π x.1) K D a b A) →
  ∀ (f : ∀ x : ι × Fin (H + 1), TorusHk (K x) (h x.1))
    (u : ∀ x : ι × Fin (H + 1), ℝ → TorusHk (K x) (h x.1))
    (W : ∀ x : ι × Fin (H + 1), ℝ → TorusHk (K x + 1) (h x.1)),
    IsCoupledWeakSolutionTorus ν a b v D K A f
      (fun _ _ => 0) (fun _ _ => 0) u W →
    ∀ t ∈ Set.Icc a b,
      massNormSq (E := fun x : ι × Fin (H + 1) => h x.1) (K := K) ρ
          (fun x => π x.1) (fun x => (u x t).val) +
        ν / 2 * ∫ r in Set.Icc a b,
          massGradNormSq (E := fun x : ι × Fin (H + 1) => h x.1) (K := K) ρ
            (fun x => π x.1) (fun x => (W x r).val) ≤
      (2 * (8 * S + 1) ^ (2 * H)) *
        massNormSq (E := fun x : ι × Fin (H + 1) => h x.1) (K := K) ρ
          (fun x => π x.1) (fun x => (f x).val)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Raw forward-copy energy at the original masses. Only the coupled energy
estimate `coupled_energy_torus` and rank-mass comparisons are used; coefficients and
the actual solution remain unchanged. Forward support is needed on the
observation window, with no chart or global support premise. -/

open CycleComparison.Error

private theorem raw_copy_rank_schur
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    {H D : ℕ} (K : ι × Fin (H + 1) → ℕ)
    (ν ρ a b : ℝ) (hν : 0 < ν) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : ∀ x y : ι × Fin (H + 1), (d : admissibleOrders K D x y) → ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h y.1)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h x.1)))
    (hfw : ∀ x y d, x.2.val ≠ y.2.val + 1 → ∀ t ∈ Set.Icc a b, A x y d t = 0)
    (S : ℝ) (hS : 0 ≤ S)
    (hschur : SchurBound S (schurMatrix ν ρ (fun x => π x.1) K D a b A)) :
    SchurCondition (schurMatrix ν ρ
      (rankScaledMass (fun x => π x.1) (fun x => x.2.val) (8 * S + 1)) K D a b A) := by
  let L := 8 * S + 1
  have hL : 1 ≤ L := le_add_of_nonneg_left (mul_nonneg (by norm_num) hS)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hb (x y : ι × Fin (H + 1)) :
      schurMatrix ν ρ (rankScaledMass (fun x => π x.1) (fun x => x.2.val) L) K D a b A x y ≤
        schurMatrix ν ρ (fun x => π x.1) K D a b A x y / L := by
    rw [schurMatrix_eq, schurMatrix_eq]
    by_cases hxy : x.2.val = y.2.val + 1
    · have hr : y.2.val < x.2.val := by omega
      have hsqrt : Real.sqrt
          (rankScaledMass (fun x => π x.1) (fun x => x.2.val) L y /
            rankScaledMass (fun x => π x.1) (fun x => x.2.val) L x) =
          Real.sqrt (π y.1 / π x.1) *
            Real.sqrt (CycleJointProofs.rankMass (fun x : ι × Fin (H + 1) => x.2.val) L y /
              CycleJointProofs.rankMass (fun x : ι × Fin (H + 1) => x.2.val) L x) := by
        unfold rankScaledMass CycleJointProofs.rankMass
        rw [mul_div_mul_comm, Real.sqrt_mul (div_nonneg (hπ y.1).le (hπ x.1).le)]
      rw [hsqrt]
      exact rankScaled_mul_le_div (Real.sqrt_nonneg _) (DescEntry_nonneg hν hρ x y)
        (CycleJointProofs.rankMass_sqrt_ratio_le_inv (fun x => x.2.val) L hL x y hr)
    · rw [DescEntry_eq_zero (fun d t ht => hfw x y d hxy t ht)]
      simp only [mul_zero, zero_div, le_refl]
  have hdiv : S / L ≤ 1 / 8 := by
    rw [div_le_iff₀ hLp]
    dsimp only [L]
    linarith only []
  refine ⟨fun x => ?_, fun y => ?_⟩
  · calc
      _ ≤ ∑ y, schurMatrix ν ρ (fun x => π x.1) K D a b A x y / L :=
        Finset.sum_le_sum fun y _ => hb x y
      _ = (∑ y, schurMatrix ν ρ (fun x => π x.1) K D a b A x y) / L :=
        (Finset.sum_div _ _ _).symm
      _ ≤ S / L := div_le_div_of_nonneg_right (hschur.1 x) hLp.le
      _ ≤ 1 / 8 := hdiv
  · calc
      _ ≤ ∑ x, schurMatrix ν ρ (fun x => π x.1) K D a b A x y / L :=
        Finset.sum_le_sum fun x _ => hb x y
      _ = (∑ x, schurMatrix ν ρ (fun x => π x.1) K D a b A x y) / L :=
        (Finset.sum_div _ _ _).symm
      _ ≤ S / L := div_le_div_of_nonneg_right (hschur.2 y) hLp.le
      _ ≤ 1 / 8 := hdiv

/-- Full raw copied energy at the original masses, for the same actual
solution, with the exact finite rank factor and no chart hypothesis. -/
theorem raw_copied_plain_energy : RawCopiedPlainEnergyStatement := by
  intro ι _ _ h _ _ _ _ _ _ H D Kmax K hD hK ν ρ a b v hν hρ hab hd
    π hπ A hfin hmeas hsmooth hper hfw S hS hschur f u W hsol t ht
  let π₀ : ι × Fin (H + 1) → ℝ := fun x => π x.1
  let r : ι × Fin (H + 1) → ℕ := fun x => x.2.val
  let L := 8 * S + 1
  let π' := rankScaledMass π₀ r L
  have hπ₀ : ∀ x, 0 < π₀ x := fun x => hπ x.1
  have hL : 1 ≤ L := le_add_of_nonneg_left (mul_nonneg (by norm_num) hS)
  have hπ' : ∀ x, 0 < π' x := rankScaledMass_pos hπ₀ (zero_lt_one.trans_le hL)
  have hschur' := raw_copy_rank_schur K ν ρ a b hν hρ π hπ A hfw S hS hschur
  obtain ⟨a', B₀, lam, ha, hB₀, hlam, hjets, hB, hstrain⟩ := hd.jets
  have hgate := coupled_energy_torus a b hab ρ hρ ν hν v hd.bdd hd.meas hd.smooth hd.div hd.per
    a' B₀ lam ha hB₀ hlam Kmax hjets hB hstrain D hD π' hπ' K hK A
    hmeas hsmooth hper hfin hschur' f (fun _ _ => 0)
    (fun _ => timeMemLp_zero _ 2) (fun _ _ => 0) (fun _ => timeIntegrable_zero _)
  have he := hgate.2.2 u W hsol t ht
  simp only [torusMassNormSq_zero K ρ π' hπ',
    Real.sqrt_zero, integral_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at he
  have hrH : ∀ x, r x ≤ H := fun x => Nat.le_of_lt_succ x.2.isLt
  have hm := massNormSq_le_rankScaledMass ρ π₀ hπ₀ r L hL H hrH (fun x => (u x t).val)
  have hdatum := massNormSq_rankScaledMass_le ρ π₀ hπ₀ r L hL (fun x => (f x).val)
  have hgrad : (∫ z in Set.Icc a b,
      massGradNormSq ρ π₀ (fun x => (W x z).val)) ≤
      L ^ (2 * H) * ∫ z in Set.Icc a b,
        massGradNormSq ρ π' (fun x => (W x z).val) := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_massGradNormSq ρ π₀ W hsol.2.1)
      ((integrable_massGradNormSq ρ π' W hsol.2.1).const_mul _)
      (fun z => massGradNormSq_le_rankScaledMass ρ π₀ hπ₀ r L hL H hrH
        (fun x => (W x z).val))
  have hνhalf : 0 ≤ ν / 2 := div_nonneg hν.le (by norm_num)
  have hLH : 0 ≤ L ^ (2 * H) := pow_nonneg (zero_le_one.trans hL) _
  calc
    _ ≤ L ^ (2 * H) * massNormSq ρ π' (fun x => (u x t).val) +
        ν / 2 * (L ^ (2 * H) * ∫ z in Set.Icc a b,
          massGradNormSq ρ π' (fun x => (W x z).val)) :=
      add_le_add hm (mul_le_mul_of_nonneg_left hgrad hνhalf)
    _ = L ^ (2 * H) * (massNormSq ρ π' (fun x => (u x t).val) +
        ν / 2 * ∫ z in Set.Icc a b,
          massGradNormSq ρ π' (fun x => (W x z).val)) := by ring
    _ ≤ L ^ (2 * H) * (2 * massNormSq ρ π' (fun x => (f x).val)) :=
      mul_le_mul_of_nonneg_left he hLH
    _ = (2 * L ^ (2 * H)) * massNormSq ρ π' (fun x => (f x).val) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdatum (mul_nonneg (by norm_num) hLH)

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The original tower and its actual native path supply the existing
buffer input, with the literal stage coefficients and kernels. The one path
is chosen before all weights/data; its finite tower is already produced.
The degenerate cases are included: Kbuf=0, empty and singleton families, constants, identity
geometry and edgeless seed stages use the same molecular delay and operator equalities.
No higher-order invariant premise or new evolution estimate is introduced. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Supply all numeric/semantic fields of the real buffer input from one
actual tower. The path is the existing native path, before every weight. -/
theorem preparation_native_buffer_input (F : Request hr D Dm bw j₀)
    {Kbuf : ℕ} {CK : ℕ → ℝ} {Θ : ℝ} (T : PreparationNativeTower F Kbuf CK Θ)
    (slow : ℝ) (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3)
    (hs₀ : 0 < slow) (hs₁ : slow < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α slow D.q) (hζ : IsFastProfile D.ζ)
    (hΛ : 128 ≤ D.Λ) (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (hi : 1 ≤ F.G.level) (hc₀ : 0 < F.c₀)
    (hcap : F.c₀ ≤ Buffer.exists_molecular_uniform_constants.choose)
    (hdelay : F.bufferEnd ≤ F.tf) :
    let P := T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩
    Nonempty (PreparationNativeBufferInput (c := F.bufferEnd) P D F.G.level Kbuf
      (F.G.mass F.law) {w | (w = fun _ => 1) ∨ w = F.G.marker F.law}) := by
  let P := T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩
  have hac : F.s ≤ F.bufferEnd := by
    exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) P.diffusivity_pos.le)
  have hφ : IsAdmissibleStream (D.Φ F.G.level) := D.hΦ F.G.level
  obtain ⟨L, hL⟩ := native_energy_path_of_operator P hφ hac
  refine ⟨{
    slow := slow
    alpha_pos := hα₀
    alpha_lt := hα₁
    slow_pos := hs₀
    slow_lt := hs₁
    admissible_q := hq
    profile := hζ
    frequency := hΛ
    stream := hseq
    level_pos := hi
    c₀ := F.c₀
    c₀_pos := hc₀
    radius_cap := hcap
    radius_formula := rfl
    delay_end := hdelay
    unit_weight := Or.inl rfl
    operators := fun w hw j => T.operators w hw j
    mass := fun w hw j => T.mass w hw j
    coefficient := fun w hw j =>
      (T.coefficient w hw j).trans (T.coefficient (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩).symm
    inclusion := fun w hw j =>
      (T.inclusion w hw j).trans (T.inclusion (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩).symm
    kernel := fun w hw j =>
      (T.kernel w hw j).trans (T.kernel (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩).symm
    path := L
    realizes := hL }⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The native-frame join uses ONE native operator tower and ONE buffered
fixed-point path, before both masses and all data. The remaining producer
only combines existing native/scalar paths and the molecular buffer.
The degenerate cases are included: empty or singleton components, Dm=2, order zero, constant/zero
data, identity geometry and an edgeless seed retain the same molecular endpoint;
no assertion is inferred by selecting a nonempty component. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule

/-- Keep the supplied actual native path while adjoining its scalar responses,
fixed point and one buffered datum before every radius and certified mass. -/
def NativePreparationFrameJoinStatement : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*}
    [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
    [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
    [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
    {a b ρ ν : ℝ} {Dm : ℕ}
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 Dm)
    (OC : OCData) (m Kbuf : ℕ) (π : ι → ℝ) (weights : Set (ι → ℝ))
    (I : PreparationNativeBufferInput (c := a + ρ ^ 2 / ν) P OC m Kbuf π weights),
    Providers.WeakGen.Comparison.TorusDriftData ν ρ (a + ρ ^ 2 / ν) b
      (streamVel (OC.Φ m)) Kbuf →
    ∃ (hac : a ≤ a + ρ ^ 2 / ν)
      (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b (a + ρ ^ 2 / ν)),
      M.full = I.path ∧
      BufferedKernelMapsRealizes P (OC.Φ m) hac I.delay_end M ∧
      M.IsFixedPoint hac I.delay_end ∧
    ∃ B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk Kbuf (h i)),
      (∀ f i, truncateTorusHk (Nat.zero_le Kbuf) (B f i) =
        (M.full f).1 ⟨a + ρ ^ 2 / ν, hac, I.delay_end⟩ i) ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ ρ → ∀ w ∈ weights, ∀ f,
        Real.sqrt (massNormSq r (fun i => π i / w i ^ 2) (fun i => (B f i).val)) ≤
          Real.sqrt (Buffer.bufferEnergyCost Kbuf) *
            Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2) (fun i => (f i).val))) ∧
      BufferedConstantTraceStatement (fun _ => Kbuf) B
end

/-! The native frame join from its one supplied-path fixed-point ingredient.
The existing buffered-slot theorem supplies the same high datum at every radius
and weight; no native path is replaced by a newly chosen evolution. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule
universe u v w z

/-- Scalar responses and their fixed point retain any supplied realized native path. -/
def SuppliedNativeFixedPointStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type w} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type z}
    [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
    [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
    [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
    {a b ρ ν : ℝ} {Dm : ℕ}
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 Dm)
    (φ : ℝ → Vec 2 → ℝ) (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (Kmax : ℕ),
    Providers.WeakGen.Comparison.TorusDriftData ν ρ c b (streamVel φ) Kmax →
    ∀ F : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b c,
      NativeEnergyPathRealizes P φ c F →
    ∃ M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c,
      M.full = F ∧ BufferedKernelMapsRealizes P φ hac hcb M ∧ M.IsFixedPoint hac hcb

/-- The supplied-path fixed point and buffering give the exact frame join. -/
theorem native_frame_join_of_fixed_point
    (hfixed : SuppliedNativeFixedPointStatement.{u, v, w, z}) :
    NativePreparationFrameJoinStatement.{u, v, w, z} := by
  intro ι _ _ h _ _ _ _ _ _ Γ _ G _ _ _ _ _ _ a b ρ ν Dm P OC m Kbuf π weights I hd
  have hac : a ≤ a + ρ ^ 2 / ν :=
    le_add_of_nonneg_right (div_nonneg (sq_nonneg ρ) P.diffusivity_pos.le)
  obtain ⟨M, hfull, hM, hfp⟩ := hfixed P (OC.Φ m) (a + ρ ^ 2 / ν)
    hac I.delay_end Kbuf hd I.path I.realizes
  obtain ⟨B, htrace, hbound, hconst⟩ := native_buffered_slot_datum I
    (fun _ => Kbuf) (fun _ => le_rfl)
  refine ⟨hac, M, hfull, hM, hfp, B, ?_, ?_, hconst⟩
  · intro f i
    rw [hfull]
    exact (htrace f i).trans (by rw [Set.projIcc_of_mem P.htime ⟨hac, I.delay_end⟩])
  · intro r hr hrρ w hw f
    have hh := hbound r hr hrρ w hw f
    simp only [CycleJointProofs.torusHkNorm_full,
      Real.sq_sqrt (factorialNormSq_nonneg r _)] at hh
    exact hh
end

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Scalar insertion fixes the supplied native path. This reuses the existing
restart/scalar uniqueness argument while keeping the full map prescribed by
the caller, including its ambient higher class. -/

attribute [local instance] preparationScalarFluxModule preparationScalarFluxSMul preparationRestartFluxAdd
  preparationResponseNativeNormed preparationResponseNativeModule
  preparationResponseDatumAdd preparationResponseDatumMonoid preparationResponseDatumModule
  preparationNativeFamilyNormed preparationNativeFamilyModule preparationNativeContinuousModule
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν : ℝ} {D : ℕ}

private theorem frame_fixed_point_of_realizations
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    {φ : ℝ → Vec 2 → ℝ} {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) {Kmax : ℕ}
    (hd : TorusDriftData ν ρ c b (streamVel φ) Kmax)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M) : M.IsFixedPoint hac hcb := by
  classical
  let Q := Buffer.kernelOperator_time_restrict P (Set.Icc_subset_Icc hac le_rfl) hcb
  let F := M.full
  let J₀ := M.homogeneous
  let Jk := M.source
  obtain ⟨hF, hJ₀, hJk⟩ := hM
  intro f
  let hn := native_energy_path_restart P hac hcb F hF f
  let W := Classical.choose hn
  let hy := Classical.choose_spec hn
  let Y := Classical.choose hy
  have hrestart := (Classical.choose_spec hy).1
  have hW := (Classical.choose_spec hy).2
  let u := fun i t => (F f).1 (Set.projIcc a b P.htime t) i
  let d := (F f).1 ⟨c, hac, hcb⟩
  let hzero := hJ₀ d
  let W₀ := Classical.choose hzero.2
  have hs₀ := (Classical.choose_spec hzero.2).1
  have hW₀ := (Classical.choose_spec hzero.2).2
  let hkernel := hJk (F f).2
  let Wk := Classical.choose hkernel.2
  have hsk := (Classical.choose_spec hkernel.2).1
  have hWk := (Classical.choose_spec hkernel.2).2
  have hraw : ∀ᵐ t ∂volume.restrict (Set.Icc c b), ∀ i, (W i t).val = (F f).2 t i := by
    filter_upwards [hW] with t ht
    intro i
    exact (congrArg (fun z : CoupledHighHilbert (h := h) (fun _ => 0) => z i) ht).symm
  have hpost := preparation_kernel_scalar_two_trace Q hd (Nat.zero_le Kmax) hrestart (F f).2 hraw hs₀ hsk
  apply preparation_buffered_maps_eq hac hcb M f (fun d => (hJ₀ d).1) (fun U => (hJk U).1)
  · intro t ht
    funext i
    have he := hpost i t ⟨ht, t.property.2⟩
    simpa only [u, d, Pi.add_apply,
      Set.projIcc_of_mem P.htime t.property,
      Set.projIcc_of_mem hcb ⟨ht, t.property.2⟩] using he
  · apply preparation_native_higher_add_of_traces c b (F f).2 (J₀ d).2
      (Jk (F f).2).2 W W₀ Wk hW hW₀ hWk
    filter_upwards [ae_all_iff.mpr hrestart.2.2.1,
      ae_all_iff.mpr (fun i => (hs₀ i).2.2.1 0),
      ae_all_iff.mpr (fun i => (hsk i).2.2.1 0),
      ae_restrict_mem measurableSet_Icc] with t htr htr₀ htrk ht
    intro i
    exact (htr i).trans ((hpost i t ht).trans
      (congrArg₂ (fun x y => x + y) (htr₀ i).symm (htrk i).symm))

/-- Adjoin scalar responses to the actual supplied native path without replacing it. -/
theorem supplied_native_fixed_point : SuppliedNativeFixedPointStatement := by
  intro ι _ _ h _ _ _ _ _ _ Γ _ G _ _ _ _ _ _ a b ρ ν Dm P φ c hac hcb Kmax hd F hF
  let Q := Buffer.kernelOperator_time_restrict P (Set.Icc_subset_Icc hac le_rfl) hcb
  obtain ⟨J₀, hJ₀⟩ := scalar_homogeneous_energy_path_of_drift (h := h)
    hd hcb P.radius_pos P.diffusivity_pos
  obtain ⟨Jk, hJk⟩ := scalar_kernel_energy_path_of_drift Q hd
  change ScalarFamilyEnergyPathRealizes (h := h) (ν := ν) hcb (streamVel φ)
    (preparationKernelScalarDatum Q) Jk at hJk
  let M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c := ⟨F, J₀, Jk⟩
  have hM : BufferedKernelMapsRealizes P φ hac hcb M := ⟨hF, hJ₀, hJk⟩
  exact ⟨M, rfl, hM, frame_fixed_point_of_realizations P hac hcb hd M hM⟩

/-- One native fixed point and one high buffered datum, before all radii and weights. -/
theorem native_preparation_frame_join : NativePreparationFrameJoinStatement :=
  native_frame_join_of_fixed_point supplied_native_fixed_point

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! One scalar environment for the actual native frame and the joint preparation of the copied
family.
The molecular cap precedes all finite requests. The entrance radius and
level floor precede every band chain, stage, stream and start time. Joining
these bounds does not choose a model or change its endpoint.
The degenerate cases are included: empty and singleton families, every interior seed, identity
geometry, edgeless stages, arbitrary buffer starts and order zero use the same scalar
choices. Terminal levels remain excluded, as in the three producers. -/

open AVRegularity.Construction.Preservation.Assembly WindowCover

/-- Scalar inputs at fixed constants and a common level floor. This is
stage-generic and contains no model, family or datum. -/
def PreparationScalarEnvironmentAt (α q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (g₀ c₀ cOld Crat : ℝ) (mStar : ℕ) : Prop :=
  ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
  ∀ m : ℕ, mStar ≤ m → m < M →
    let ρ := c₀ * min (ocEpsilon q Λ m) (Real.sqrt (κ m / ocA α q Λ m))
    let ρold := cOld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q)
    (ρ = ocRhoMol α q Λ m c₀ (κ m) ∧ 0 < ρold ∧ ρold ≤ ρ ∧
      ρ / ρold ≤ Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))) ∧
    ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ), IsOCStreamSeq α q Λ ζ Φ →
      ρ ^ 2 / κ m ≤ 2 * ocTauPP α q Λ m ∧
      (∀ (a b : ℝ) (Kmax : ℕ), Providers.WeakGen.Comparison.TorusDriftData
        (κ m) ρ a b (streamVel (Φ m)) Kmax) ∧
      ∀ (hφ : IsAdmissibleStream (Φ (m - 1))) (t₁ : ℝ) (qJ Kmax : ℕ),
      ∃ (l₀ : ℤ) (P : ℕ), 1 ≤ P ∧
        ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ t₁ ∧
        t₁ < ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m ∧
        t₁ + 2 * ocTauPP α q Λ m ≤ ((l₀ : ℝ) + P - 1 / 2) * ocTauPP α q Λ m ∧
        CommonPreparationWindowCoverStatement α q Λ m ζ Φ hφ (κ m) (κ (m - 1))
          t₁ 2 c₀ (windowCoverCg * (ocA α q Λ (m - 1) * ocTauPP α q Λ m)) g₀
          (windowCoverCd * ocA α q Λ m * ocEpsilon q Λ m ^ 2 / κ m)
          windowCoverB0 1 windowCoverCb qJ Kmax windowCoverCG l₀ P 0


/-- The simultaneous radius, delay, drift and cover inputs at one common
frequency/radius/level threshold, before actual stage data are supplied. -/
def PreparationScalarEnvironmentStatement (α q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∃ cmax : ℝ, 0 < cmax ∧
    cmax ≤ Buffer.exists_molecular_uniform_constants.choose ∧ cmax ≤ 1 ∧
  ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ g₀ c₀ : ℝ, 0 < g₀ → 0 < c₀ → c₀ ≤ cmax →
  ∃ cOld Crat : ℝ, 0 < cOld ∧ 0 < Crat ∧ ∃ mStar : ℕ, 2 ≤ mStar ∧
    PreparationScalarEnvironmentAt α q ζ Λ g₀ c₀ cOld Crat mStar

/-- Join the three already proved scalar producers without moving any
choice behind the stage, the stream, a finite request or the actual datum. -/
theorem preparation_scalar_environment {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    PreparationScalarEnvironmentStatement α q ζ := by
  obtain ⟨Λd, hΛd, cd, hcd, hcdb, hd⟩ :=
    native_preparation_drift hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λr, _hΛr, hr⟩ := preparation_joint_radius_scales hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λc, _hΛc, cc, hcc, hc⟩ := cascadePreparationCover hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λd (max Λr Λc), hΛd.trans (le_max_left _ _),
    min 1 (min cd cc), lt_min zero_lt_one (lt_min hcd hcc),
    ((min_le_right _ _).trans (min_le_left _ _)).trans hcdb, min_le_left _ _, ?_⟩
  intro Λ hΛ g₀ c₀ hg₀ hc₀ hcmax
  have hc₀d : c₀ ≤ cd := hcmax.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc₀c : c₀ ≤ cc := hcmax.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨md, hmd, hd⟩ := hd Λ ((le_max_left _ _).trans hΛ) c₀ hc₀ hc₀d
  obtain ⟨cOld, Crat, hcOld, hCrat, mr, _hmr, hr⟩ :=
    hr Λ (((le_max_left _ _).trans (le_max_right _ _)).trans hΛ) c₀ hc₀
  obtain ⟨mc, _hmc, hc⟩ :=
    hc Λ (((le_max_right _ _).trans (le_max_right _ _)).trans hΛ) g₀ c₀ hg₀ hc₀ hc₀c
  refine ⟨cOld, Crat, hcOld, hCrat, max md (max mr mc),
    hmd.trans (le_max_left _ _), ?_⟩
  intro M κ hband m hm hmM
  have hmdm : md ≤ m := (le_max_left _ _).trans hm
  have hmrm : mr ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans hm
  have hmcm : mc ≤ m := ((le_max_right _ _).trans (le_max_right _ _)).trans hm
  refine ⟨hr M κ hband m hmrm hmM, ?_⟩
  intro Φ hΦ
  have hdrift := hd M κ hband m hmdm hmM Φ hΦ
  exact ⟨hdrift.1, hdrift.2, hc M κ hband m hmcm hmM Φ hΦ⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance Filter
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.KernelDefect
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The moment defect at an individual derivative level, and its cost in the
actual gradient energy. These retain the gradient rather than estimating it
by the value norm, as required by the plain-source energy estimate.

The degenerate cases are included: zero data and constants have their actual defect, L=0 is
boundedness, the first derivative costs no shift, and rho=width has moment factor one.
The componentwise statements cover empty and singleton families, D=2,
identity geometry and edgeless seeds without a component-count constant. -/

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
private theorem preparation_plain_derivative_energy_continuous {K : ℕ}
    (j : Fin (K + 1)) :
    Continuous (fun u : TorusHk K E => derivativeNormSq u.val j) := by
  unfold derivativeNormSq
  apply continuous_finsetSum
  intro w _
  exact (((PiLp.proj (𝕜 := ℝ) 2
    (fun _ : JetIndex2 K => Lp E 2 (volume.restrict unitCube)) ⟨j, w⟩).continuous.comp
      continuous_subtype_val).norm.pow 2)

omit [FiniteDimensional ℝ E] in
private theorem preparation_plain_defect_derivative_continuous
    {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀) (S : KernelSpec) (t : ℝ)
    (k L : ℕ) (j : Fin (k + 1)) :
    Continuous (fun u : TorusHk (k + L) E =>
      derivativeNormSq (kdRealization φ₀ hφ S t u).val j) := by
  unfold derivativeNormSq
  apply continuous_finsetSum
  intro w _
  let β := truncateJetIndex (Nat.le_add_right k L) (⟨j, w⟩ : JetIndex2 k)
  have hc : Continuous (fun u : TorusHk (k + L) E => u.val β) :=
    (PiLp.proj (𝕜 := ℝ) 2
      (fun _ : JetIndex2 (k + L) => Lp E 2 (volume.restrict unitCube)) β).continuous.comp
        continuous_subtype_val
  change Continuous (fun u : TorusHk (k + L) E =>
    ‖u.val β - S.op φ₀ hφ t (u.val β)‖ ^ 2)
  exact (hc.sub ((S.op φ₀ hφ t).continuous.comp hc)).norm.pow 2

/-- The exact derivative-level moment estimate holds for every rough input.
Its constant precedes the kernel, time and datum, and is independent of
the kernel order and k. The shared order reduction supplies this uniformity. -/
theorem preparation_plain_defect_jet_le {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z)
    (hmass : ∫ z, φ₀ z = 1)
    (hsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (L : ℕ) (Γ : ℝ) (S : KernelSpec) (t : ℝ)
    (hadm : S.IsAdmissible Γ L) (hr : 0 < S.width)
    {k : ℕ} (u : TorusHk (k + L) E) (j : ℕ) (hj : j ≤ k) :
    derivativeNormSq (kdRealization φ₀ hφ S t u).val ⟨j, by omega⟩ ≤
      (kdUniformMomentConst φ₀ L |Γ| * S.width ^ L) ^ 2 *
        derivativeNormSq u.val ⟨j + L, by omega⟩ := by
  obtain ⟨_, _, hH, hL⟩ := hadm
  have hproj (a : ℕ) := kdRealization_jet_le_of_order_le hφ hd hnonneg hmass hsupp
    L (kdUniformOrder L) |Γ| S t (kdUniformOrder_le hL) (kdUniformOrder_spec L) hr ((hH t).1.trans (le_abs_self Γ)) ((hH t).2.1.trans (le_abs_self Γ))
    (galerkinProj a u) _ (galerkinProj_isClassicalRep_explicit a u (le_refl (k + L))) hj
  have hleft := ((preparation_plain_defect_derivative_continuous hφ S t k L
    ⟨j, by omega⟩).tendsto u).comp (galerkinProj_tendsto u)
  have hright := (((preparation_plain_derivative_energy_continuous
    ⟨j + L, by omega⟩).tendsto u).comp (galerkinProj_tendsto u)).const_mul
      ((kdUniformMomentConst φ₀ L |Γ| * S.width ^ L) ^ 2)
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hproj)

omit [FiniteDimensional ℝ E] in
/-- Extracting one higher derivative from gradient energy costs its factorial
shift, with no extra inverse radius for the already-present gradient. -/
theorem preparation_plain_gradient_level_le (ρ : ℝ) (hρ : 0 < ρ) {K : ℕ}
    (u : TorusHk (K + 1) E) (j : Fin (K + 1)) :
    derivativeNormSq u.val ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ ≤
      (derivativeReserveFactor ρ 0 j.val) ^ 2 * gradFactorialNormSq ρ u.val := by
  have hw : (1 : ℝ) ≤ (derivativeReserveFactor ρ 0 j.val) ^ 2 *
      factorialWeight ρ j.val := by
    simpa only [factorialWeight, Nat.factorial_zero, Nat.cast_one, pow_zero,
      one_div, inv_one, Nat.zero_add, mul_one, Nat.mul_zero, one_pow, div_one] using
      (factorialWeight_reserve_le ρ hρ (j := 0) (K := 0) (le_refl 0) j.val)
  have hlevel : factorialWeight ρ j.val *
      derivativeNormSq u.val ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ ≤
      gradFactorialNormSq ρ u.val := by
    change factorialWeight ρ j.val * derivativeNormSq u.val _ ≤
      ∑ i : Fin (K + 1), factorialWeight ρ i.val *
        derivativeNormSq u.val ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    exact Finset.single_le_sum (f := fun i : Fin (K + 1) => factorialWeight ρ i.val *
      derivativeNormSq u.val ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i _ => mul_nonneg (factorialWeight_nonneg ρ i.val)
        (derivativeNormSq_nonneg u.val _)) (Finset.mem_univ j)
  calc
    _ = 1 * derivativeNormSq u.val ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := (one_mul _).symm
    _ ≤ ((derivativeReserveFactor ρ 0 j.val) ^ 2 * factorialWeight ρ j.val) *
        derivativeNormSq u.val ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ :=
      mul_le_mul_of_nonneg_right hw (derivativeNormSq_nonneg u.val _)
    _ = (derivativeReserveFactor ρ 0 j.val) ^ 2 *
        (factorialWeight ρ j.val * derivativeNormSq u.val
          ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hlevel (sq_nonneg _)

variable {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

omit [FiniteDimensional ℝ E] in
/-- A constant coefficient map and a truncation preserve the exact level
bound with the squared operator norm. -/
theorem preparation_plain_mapped_level_le {k K : ℕ} (hk : k ≤ K)
    (C : E →L[ℝ] G) (u : TorusHk K E) (j : Fin (k + 1)) :
    derivativeNormSq (mapTorusHk C (truncateTorusHk hk u)).val j ≤
      ‖C‖ ^ 2 * derivativeNormSq u.val ⟨j.val, by omega⟩ := by
  unfold derivativeNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  rw [mapTorusHk_jet_eq_compLp]
  exact (pow_le_pow_left₀ (norm_nonneg _) (C.norm_compLp_le _) 2).trans_eq
    (mul_pow _ _ _)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
