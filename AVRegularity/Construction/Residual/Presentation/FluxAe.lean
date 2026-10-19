-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.Local
public import AVRegularity.Definitions.Families.ActualFamily
import AVRegularity.EntryWeakAssembly.MolecularHigherTraceJetDerivative
public import AVRegularity.Statements.Intermediate.CycleOutput.OcChartInv
import AVRegularity.Construction.Preservation.Residual.KernelReadout.ClassicalComponent
import AVRegularity.Proofs.WeakGen.Comparison.GateInputs
import AVRegularity.IterationPassage.Passage.Profiles.ClausesStatement
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
public import AVRegularity.KernelEnergy.TorusTimeFlux
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
public import AVRegularity.Statements.Intermediate.Families.FamilyEdges
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup
import Mathlib.CategoryTheory.Countable

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **The glued lift of the interior reconstruction at a stage is the lifted field of the stage**.

The interior physical reconstruction (`cycle_comparison_physical_lift`, `ReconWindow`) concludes
about the glued lift over the pulses observed on the whole window `[t_p, t_f]`, with the weights of
the charted family, the cell time `ℓ² = (ε_m/√ν)²`, the slow length `√(Bτ_m'')` and the renewal
charts `ocChart` at the chart index `ocPulseChartIndex`. The lifted field of a stage
(`liftedRep`, `menuLiftedRep`) is the glued lift over the pulses observed at the time `t`, with
the cutoffs `ocCutoff`, the cell time `D.cellScaleSq m`, the slow length
`Mn.lenFactor · liftLength D m` and the flows from the slot anchors `l_{m,k}τ_m''`.

At a time of the window they are equal (`stage_gluedLift_eq_menuLiftedRep`), when
- the weights of the family are the cutoffs (`GenStage.IsNatural`, second clause);
- the slow length factor of the menu is `1` (the cascade menu; the terminal menu at `c_r = 1`);
- `m ≤ D.term` and `0 ≤ κ_m` (the cell diffusivity is `κ_m`);
- `1 ≤ Λ` (the renewal period is positive: `ocLabel_eq_ocPulseChartIndex`).
The lift coefficients are the same array on both sides: the identification of the lift windows and
of the lift operator data is a separate matter.

Remarks. For `t_p = t_f = t` the two pulse sets coincide, and an even integer is in neither
pulse set. A pulse of the window whose lift window does not contain `t` has weight `0` at `t`
  (`ocCutoff_zero_off_output`). -/

/-- The odd slot of an integer (the slot `1` for an even integer): the piece of the stage's family
that carries the pulse `k`. -/
def oddSlotOf (k : ℤ) : OddSlot := if h : Odd k then ⟨k, h⟩ else ⟨1, odd_one⟩

theorem oddSlotOf_of_odd {k : ℤ} (h : Odd k) : oddSlotOf k = ⟨k, h⟩ := by
  simp only [oddSlotOf, h, ↓reduceDIte]

/-- `oddSlotOf` is injective on odd integers. -/
theorem oddSlotOf_injOn : Set.InjOn oddSlotOf {k : ℤ | Odd k} := by
  intro k hk l hl hkl
  rw [oddSlotOf_of_odd hk, oddSlotOf_of_odd hl] at hkl
  exact congrArg Subtype.val hkl

/-- The pulses observed at a time of the window are observed on the window. -/
theorem obsPulses_time_subset (α q : ℝ) (Λ m : ℕ) (hτ : 0 < ocTau α q Λ m) {tp tf t : ℝ}
    (ht : t ∈ Set.Icc tp tf) : ocObsPulses α q Λ m t t ⊆ ocObsPulses α q Λ m tp tf := by
  classical
  intro k hk
  unfold ocObsPulses at hk ⊢
  obtain ⟨hI, hodd, s, hs, hst⟩ := Finset.mem_filter.1 hk
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.1 hI
  refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, hodd, s, hs, ?_⟩
  · have := Int.floor_mono (div_le_div_of_nonneg_right ht.1 hτ.le)
    omega
  · have := Int.ceil_mono (div_le_div_of_nonneg_right ht.2 hτ.le)
    omega
  · exact ⟨ht.1.trans hst.1, hst.2.trans ht.2⟩

/-- An odd integer whose lift window contains `t` is observed at `t`. -/
theorem mem_obsPulses_time (α q : ℝ) (Λ m : ℕ) (hτ : 0 < ocTau α q Λ m) {k : ℤ} (hodd : Odd k)
    {t : ℝ} (ht : t ∈ ocPulseWindow α q Λ m k) : k ∈ ocObsPulses α q Λ m t t := by
  classical
  unfold ocObsPulses
  unfold ocPulseWindow at ht
  obtain ⟨h1, h2⟩ := ht
  have hk1 : (k : ℝ) - 61 / 48 ≤ t / ocTau α q Λ m := (le_div_iff₀ hτ).2 h1
  have hk2 : t / ocTau α q Λ m ≤ (k : ℝ) + 61 / 48 := (div_le_iff₀ hτ).2 h2
  refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, hodd, t, ⟨h1, h2⟩, le_rfl, le_rfl⟩
  · have hfl : ((⌊t / ocTau α q Λ m⌋ : ℤ) : ℝ) ≤ t / ocTau α q Λ m := Int.floor_le _
    have h3 : ((⌊t / ocTau α q Λ m⌋ - 2 : ℤ) : ℝ) < (k : ℝ) := by
      push_cast
      linarith
    have h4 : ⌊t / ocTau α q Λ m⌋ - 2 < k := by exact_mod_cast h3
    omega
  · have hce : t / ocTau α q Λ m ≤ ((⌈t / ocTau α q Λ m⌉ : ℤ) : ℝ) := Int.le_ceil _
    have h3 : (k : ℝ) < ((⌈t / ocTau α q Λ m⌉ + 2 : ℤ) : ℝ) := by
      push_cast
      linarith
    have h4 : k < ⌈t / ocTau α q Λ m⌉ + 2 := by exact_mod_cast h3
    omega

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The glued lift of the interior reconstruction at a stage is the lifted field of the menu.**
At a time of the window, for a family whose weights are the cutoffs and a menu of slow length
factor `1`. -/
theorem stage_gluedLift_eq_menuLiftedRep (G : GenStage D hr Dm b j₀) (Mn : SuccMenu)
    (m N depth : ℕ) (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) {tp tf t : ℝ} (x : Vec 2)
    (hΛ : 1 ≤ D.Λ) (hm : m ≤ D.term) (hκ : 0 ≤ D.κ m) (hlen : Mn.lenFactor = 1)
    (hw : ∀ (p : OddSlot) (s : ℝ), G.fam.weight p s = ocCutoff D.α D.q D.Λ m p.1 s)
    (ht : t ∈ Set.Icc tp tf) :
    gluedLift (ocObsPulses D.α D.q D.Λ m tp tf) (fun k => G.actualFamily.weight (oddSlotOf k))
        (ocEll D.q D.Λ m (D.κ m) ^ 2) (Real.sqrt (D.κ (m - 1) * ocTauPP D.α D.q D.Λ m))
        (ocEpsilon D.q D.Λ m)
        (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) /
          Real.sqrt (D.κ (m - 1) * ocTauPP D.α D.q D.Λ m)) N depth CcT
        (fun k => ocChart D.α D.q D.Λ m (D.Φ (m - 1)) (D.hΦ (m - 1))
          (ocPulseChartIndex D.α D.q D.Λ m k))
        (fun k => ocChartInv D.α D.q D.Λ m (D.Φ (m - 1)) (D.hΦ (m - 1))
          (ocPulseChartIndex D.α D.q D.Λ m k)) aRep t x =
      menuLiftedRep Mn G m N depth CcT aRep t x := by
  classical
  have hτ : 0 < ocTau D.α D.q D.Λ m := AVRegularity.Construction.Stream.ocTau_pos hΛ
  have hτ'' : 0 < ocTauPP D.α D.q D.Λ m := AVRegularity.Construction.Stream.ocTauPP_pos hΛ
  have hc : ocEll D.q D.Λ m (D.κ m) ^ 2 = D.cellScaleSq m := by
    unfold ocEll OCData.cellScaleSq OCData.kap OCData.eps
    rw [min_eq_left hm, div_pow, Real.sq_sqrt hκ]
  have hchart : ∀ k : ℤ, ocChart D.α D.q D.Λ m (D.Φ (m - 1)) (D.hΦ (m - 1))
      (ocPulseChartIndex D.α D.q D.Λ m k) =
        fun s' y => D.flowOf (m - 1) s' y (D.slotAnchor m k) := by
    intro k
    funext s' y
    unfold ocChart OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex D.α D.q D.Λ m k hτ'']
  have hinv : ∀ k : ℤ, ocChartInv D.α D.q D.Λ m (D.Φ (m - 1)) (D.hΦ (m - 1))
      (ocPulseChartIndex D.α D.q D.Λ m k) =
        fun s' y => D.flowOf (m - 1) (D.slotAnchor m k) y s' := by
    intro k
    funext s' y
    unfold ocChartInv OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex D.α D.q D.Λ m k hτ'']
  have hweight : ∀ k ∈ ocObsPulses D.α D.q D.Λ m tp tf,
      G.actualFamily.weight (oddSlotOf k) t = ocCutoff D.α D.q D.Λ m k t := by
    intro k hk
    have hodd : Odd k := by
      unfold ocObsPulses at hk
      exact (Finset.mem_filter.1 hk).2.1
    rw [oddSlotOf_of_odd hodd]
    exact hw ⟨k, hodd⟩ t
  unfold menuLiftedRep gluedLift
  simp only [hlen, one_mul, hc, hchart, hinv]
  rw [Finset.sum_congr rfl fun k hk => by rw [hweight k hk]]
  symm
  refine Finset.sum_subset (obsPulses_time_subset D.α D.q D.Λ m hτ ht) fun k hk hnk => ?_
  have hodd : Odd k := by
    unfold ocObsPulses at hk
    exact (Finset.mem_filter.1 hk).2.1
  have hout : t ∉ ocPulseWindow D.α D.q D.Λ m k := fun hin =>
    hnk (mem_obsPulses_time D.α D.q D.Λ m hτ hodd hin)
  rw [AVRegularity.WeakEntryProofs.ocCutoff_zero_off_output D.α D.q D.Λ m hτ k t hout, zero_smul]

end AVRegularity.Construction.Residual.Presentation
end
end

section
section
/-! **The identification of the omitted flux, stated generically** (the bill-residual design).

For a stage `G'`, a retained family `Gr`, a classical representative `aY` of a trajectory `Yw` of
the retained family at one time `t`, and kernel-lifted edge inputs `yom` whose values at `t` are the
kernel operators applied to the values of `Yw`, the omitted flux of `yom` equals
`omittedFluxClassical` of `aY` almost everywhere on the cell. The construction `kernelLiftYom`
of such a `yom` from a trajectory of the order `k + D_m - 1` is included.

No terminal context occurs here. For an empty retained family both sides are `0`, and for
width-0 kernels (`S = I`) both sides are the plain flux of `aY`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Analysis.Convolution

namespace AVRegularity.Construction.Residual.Presentation

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- **The generic identification** of the omitted flux: at a time `t`, if `aY t` represents
`Yw · t` classically at its order `kY` (which is at least `D_m - 1`) and the values of `yom` at `t`
are the kernel operators applied to the values of `Yw · t`, then `omittedFlux = omittedFluxClassical`
almost everywhere on the cell. -/
theorem omittedFlux_ae_eq_classical (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφc : HasCompactSupport φ₀) (G' Gr : GenStage D hr Dm b j₀) (isRet : Comp → Prop)
    (hret : ∀ u : CompIn G'.comps, isRet u.1 ↔ u.1 ∈ Gr.comps) {k kY : ℕ} (hkY : Dm - 1 ≤ kY)
    (Yw : ∀ u : CompIn Gr.comps, ℝ → TorusHk kY (hr u.1.root))
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, hr v.1.root)
    (yom : ∀ v u (_ : G'.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)) (t : ℝ)
    (hY : ∀ u, IsClassicalRep (Yw u t) (fun x => aY t x u) kY)
    (hv : ∀ v u (γ : G'.fam.Γ v u) (hu : u.1 ∈ Gr.comps),
      (yom v u γ t).val (valueIndex2 (k + Dm - 1)) =
        (G'.kernelOf P seedK freshK v u γ).op φ₀ hφ₀ t ((Yw ⟨u.1, hu⟩ t).val (valueIndex2 kY)))
    (v : CompIn G'.comps) :
    omittedFlux G' k isRet yom v t =ᵐ[volume.restrict unitCube]
      omittedFluxClassical P seedK freshK φ₀ G' Gr aY v t := by
  have hj (u : CompIn G'.comps) : ∀ᵐ x ∂(volume.restrict unitCube), ∀ hu : u.1 ∈ Gr.comps,
      ∀ (γ : G'.fam.Γ v u) (d : Finset.Icc 2 Dm) (w : DerivativeWord2 (d.1 - 1)),
      (yom v u γ t).toFunction.jet ⟨⟨d.1 - 1, by have := Finset.mem_Icc.mp d.2; omega⟩, w⟩ x =
        orderedDerivative w ((G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t
          (fun y => aY t y ⟨u.1, hu⟩)) x := by
    by_cases hu : u.1 ∈ Gr.comps
    · have h1 : ∀ (γ : G'.fam.Γ v u) (d : Finset.Icc 2 Dm) (w : DerivativeWord2 (d.1 - 1)),
          ∀ᵐ x ∂(volume.restrict unitCube),
          (yom v u γ t).toFunction.jet ⟨⟨d.1 - 1, by have := Finset.mem_Icc.mp d.2; omega⟩, w⟩ x =
            orderedDerivative w ((G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t
              (fun y => aY t y ⟨u.1, hu⟩)) x := by
        intro γ d w
        have hd := Finset.mem_Icc.mp d.2
        exact Construction.Preservation.Residual.kernel_readout_kernel_lift_jet hφ₀ hφs hφc _ t
          (Yw ⟨u.1, hu⟩ t) (yom v u γ t) (fun y => aY t y ⟨u.1, hu⟩) (hY ⟨u.1, hu⟩)
          (hv v u γ hu) (by omega) (by omega) w
      filter_upwards [ae_all_iff.mpr (fun γ => ae_all_iff.mpr (fun d =>
        ae_all_iff.mpr (fun w => h1 γ d w)))] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hu
  filter_upwards [ae_all_iff.mpr hj] with x hx
  unfold omittedFlux omittedFluxClassical
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u.1 ∈ Gr.comps
  · have hr1 : isRet u.1 := (hret u).2 hu
    simp only [hr1, hu, ↓reduceIte, ↓reduceDIte]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun d _ => ?_
    congr 1
    exact congrArg (WithLp.toLp 2) (funext (hx u hu γ d))
  · have hr1 : ¬ isRet u.1 := fun h => hu ((hret u).1 h)
    simp only [hr1, hu, ↓reduceIte, ↓reduceDIte]

open scoped Classical in
/-- **The kernel-lifted edge inputs** built from a trajectory `Zhi` of the order `k + D_m - 1`:
on the edges out of the retained family, the paired smoothing of `Zhi`; zero elsewhere. -/
def kernelLiftYom (P : ProvParams) (seedK freshK : ℕ → KernelSpec) {φ₀ : Vec 2 → ℝ}
    (hφ₀ : Integrable φ₀) (G' Gr : GenStage D hr Dm b j₀) (k : ℕ)
    (Zhi : ∀ u : CompIn Gr.comps, ℝ → TorusHk (k + Dm - 1) (hr u.1.root)) :
    ∀ v u (_ : G'.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root) :=
  fun v u γ t => if hu : u.1 ∈ Gr.comps then
    pairedTorusMomentSmoothing (G'.kernelOf P seedK freshK v u γ).width
      ((G'.kernelOf P seedK freshK v u γ).H₁ t) ((G'.kernelOf P seedK freshK v u γ).H₂ t) hφ₀
      (G'.kernelOf P seedK freshK v u γ).order (Zhi ⟨u.1, hu⟩ t)
  else 0

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The values of `kernelLiftYom` are the kernel operators applied to the values of `Zhi`. -/
theorem kernelLiftYom_val (P : ProvParams) (seedK freshK : ℕ → KernelSpec) {φ₀ : Vec 2 → ℝ}
    (hφ₀ : Integrable φ₀) (G' Gr : GenStage D hr Dm b j₀) (k : ℕ)
    (Zhi : ∀ u : CompIn Gr.comps, ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (hu : u.1 ∈ Gr.comps) (t : ℝ) :
    (kernelLiftYom P seedK freshK hφ₀ G' Gr k Zhi v u γ t).val (valueIndex2 (k + Dm - 1)) =
      (G'.kernelOf P seedK freshK v u γ).op φ₀ hφ₀ t
        ((Zhi ⟨u.1, hu⟩ t).val (valueIndex2 (k + Dm - 1))) := by
  simp only [kernelLiftYom, hu, ↓reduceDIte]
  rfl

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **The kernel inputs of the plain-to-kernel passage**.

At a stage `G`, the regularizer clause of the stage invariant (module `Construction.Invariant`,
clause 4 of the kernels) at the order `k` lifts a trajectory `W u : ℝ → H^{k+1}` to the kernel
inputs `ŷ_{vuγ}(t) ∈ H^{k+D_m-1}` with `ŷ(t) = S_{vuγ}(t) W_u(t)` in value.

* `isSpatialRegularizerTorus_mono_window`: the regularizer clause restricts to a sub-window;
* `kerInput`: the inputs, `clampedRegularizedInputCLM` of the regularizer on the window `[t_p,t_f]`;
* `kerInput_memLp`, `kerInput_value`: square integrability in time and the value clause.

The maps are linear, so `W = 0` gives `ŷ = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.KernelEnergy

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- The regularizer clause restricts to a sub-window. -/
theorem isSpatialRegularizerTorus_mono_window {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
    [CompleteSpace G] {ρ : ℝ} {k D : ℕ} {a b a' b' : ℝ} {c : ℕ → ℝ} {r : ℝ}
    {S : ℝ → (Lp G 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp G 2 (volume.restrict AVenhance.unitCube))}
    (hS : IsSpatialRegularizerTorus ρ k D a b c r S) (ha : a ≤ a') (hb : b' ≤ b) :
    IsSpatialRegularizerTorus ρ k D a' b' c r S := by
  have hsub : Set.Icc a' b' ⊆ Set.Icc a b := Set.Icc_subset_Icc ha hb
  refine ⟨fun z => ?_, fun t ht => hS.2.1 t (hsub ht), hS.2.2.1,
    fun t ht => hS.2.2.2 t (hsub ht)⟩
  exact (hS.1 z).comp_measurable (measurable_inclusion hsub)

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The kernel inputs: the regularizer lift of `W` for every identity of the stage. -/
def kerInput (G : GenStage D hr Dm b j₀) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (k : ℕ) (hD : 2 ≤ Dm) (tp tf : ℝ) (htf : tp ≤ tf)
    (c : ℕ → ℝ)
    (hS : ∀ v u (γ : G.fam.Γ v u), IsSpatialRegularizerTorus 1 k Dm tp tf c
      (G.kernelOf P seedK freshK v u γ).width (G.sysS P seedK freshK φ₀ hφ₀ v u γ))
    (W : ∀ u : CompIn G.comps, ℝ → TorusHk (k + 1) (hr u.1.root)) :
    ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root) :=
  fun v u γ t => clampedRegularizedInputCLM 1 k Dm hD tp tf c
    (G.kernelOf P seedK freshK v u γ).width (ContinuousLinearMap.id ℝ (hr u.1.root))
    (G.sysS P seedK freshK φ₀ hφ₀ v u γ) (hS v u γ) one_pos htf t (W u t)

/-- The kernel inputs are square integrable in time. -/
theorem kerInput_memLp (G : GenStage D hr Dm b j₀) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (k : ℕ)
    (hD : 2 ≤ Dm) (tp tf : ℝ) (htf : tp ≤ tf) (c : ℕ → ℝ)
    (hS : ∀ v u (γ : G.fam.Γ v u), IsSpatialRegularizerTorus 1 k Dm tp tf c
      (G.kernelOf P seedK freshK v u γ).width (G.sysS P seedK freshK φ₀ hφ₀ v u γ))
    (W : ∀ u : CompIn G.comps, ℝ → TorusHk (k + 1) (hr u.1.root))
    (hW : ∀ u, MemLp (W u) 2 (volume.restrict (Set.Icc tp tf))) (v u : CompIn G.comps)
    (γ : G.fam.Γ v u) :
    MemLp (kerInput G P seedK freshK φ₀ hφ₀ k hD tp tf htf c hS W v u γ) 2
      (volume.restrict (Set.Icc tp tf)) :=
  clampedRegularizedInput_memLp 1 k Dm hD tp tf c (G.kernelOf P seedK freshK v u γ).width
    (ContinuousLinearMap.id ℝ (hr u.1.root)) (G.sysS P seedK freshK φ₀ hφ₀ v u γ) (hS v u γ)
    one_pos htf (W u) (hW u)

/-- The value clause of the kernel inputs, at every time of the window. -/
theorem kerInput_value (G : GenStage D hr Dm b j₀) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (k : ℕ)
    (hD : 2 ≤ Dm) (tp tf : ℝ) (htf : tp ≤ tf) (c : ℕ → ℝ)
    (hS : ∀ v u (γ : G.fam.Γ v u), IsSpatialRegularizerTorus 1 k Dm tp tf c
      (G.kernelOf P seedK freshK v u γ).width (G.sysS P seedK freshK φ₀ hφ₀ v u γ))
    (W : ∀ u : CompIn G.comps, ℝ → TorusHk (k + 1) (hr u.1.root)) (v u : CompIn G.comps)
    (γ : G.fam.Γ v u) (t : ℝ) (ht : t ∈ Set.Icc tp tf) :
    (kerInput G P seedK freshK φ₀ hφ₀ k hD tp tf htf c hS W v u γ t).val
        (valueIndex2 (k + Dm - 1)) =
      G.sysS P seedK freshK φ₀ hφ₀ v u γ t ((W u t).val (valueIndex2 (k + 1))) := by
  change (torusRegularizedInput 1 k Dm hD tp tf c (G.kernelOf P seedK freshK v u γ).width
    (ContinuousLinearMap.id ℝ (hr u.1.root)) (G.sysS P seedK freshK φ₀ hφ₀ v u γ) (hS v u γ)
    (Set.projIcc tp tf htf t) (Set.projIcc tp tf htf t).property (W u t)).val _ = _
  rw [torusRegularizedInput_value, Set.projIcc_of_mem htf ht]
  simp only [Providers.WeakGen.Comparison.id_compLp_eq]

/-- At a time where the carrier vanishes the kernel inputs vanish. -/
theorem kerInput_zero (G : GenStage D hr Dm b j₀) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (k : ℕ)
    (hD : 2 ≤ Dm) (tp tf : ℝ) (htf : tp ≤ tf) (c : ℕ → ℝ)
    (hS : ∀ v u (γ : G.fam.Γ v u), IsSpatialRegularizerTorus 1 k Dm tp tf c
      (G.kernelOf P seedK freshK v u γ).width (G.sysS P seedK freshK φ₀ hφ₀ v u γ))
    (W : ∀ u : CompIn G.comps, ℝ → TorusHk (k + 1) (hr u.1.root)) (v u : CompIn G.comps)
    (γ : G.fam.Γ v u) (t : ℝ) (h0 : W u t = 0) :
    kerInput G P seedK freshK φ₀ hφ₀ k hD tp tf htf c hS W v u γ t = 0 := by
  unfold kerInput
  rw [h0, map_zero]

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The fluxes of the plain and of the kernel system, at one time**.

At a time `s`, let `wK j s` be classical representatives of `uh s ·` (`IsClassicalRep`), `Y` the
kernel inputs with `Y = S_γ (uh s)` in jets up to the common orders, and `ff` a realization of the
fine flux. Then almost everywhere in `x`, the plain flux of the lifts (the edge coefficients at
the admissible orders) is the kernel flux of the inputs plus the fine flux.

* `physCoeff_zero_of_not_admissible`: the coefficients vanish at the non-admissible orders;
* `edge_apply_eq_sum`: an edge coefficient is the sum of the physical coefficients of its identities;
* `classicalRepJetsAeAll`: the jets of a classical representative, all orders at once;
* `flux_jets_ae`: the jets of the kernel input are the classical derivatives of `S uh`
  (`kernel_readout_kernel_lift_jet`);
* `plain_flux_eq_kernel_add_fine`: the identity.

For `S = I` (width `0`) one has `fineFluxF = 0` and `Y` is the jets of `uh`; with no edges all
fluxes are `0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Analysis.Convolution

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The coefficients of the identities vanish at the non-admissible orders. -/
theorem physCoeff_zero_of_not_admissible (G : GenStage D hr Dm b j₀) (K : CompIn G.comps → ℕ)
    (hdesc : G.fam.IsDescending K) (v j : CompIn G.comps) (α : G.fam.Γ v j) (n : ℕ)
    (hn : n ∈ Finset.Icc 2 Dm) (hna : n ∉ admissibleOrders K Dm v j) (s : ℝ) (x : Vec 2) :
    G.physCoeff v j α n s x = 0 := by
  have hmax := hdesc v j α
  have h1 : ¬ (K v + n ≤ K j + 2) := fun h => hna (Finset.mem_filter.2 ⟨hn, h⟩)
  rw [GenStage.physCoeff]
  exact CycleJointProofs.constituentPhysical_zero_above_max G.fam _ _ _ G.actual v j α n
    (by omega) s x

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- An edge coefficient is the sum of the physical coefficients of its identities. -/
theorem edge_apply_eq_sum (G : GenStage D hr Dm b j₀) (K : CompIn G.comps → ℕ)
    (v j : CompIn G.comps) (d : admissibleOrders K Dm v j) (s : ℝ) (x : Vec 2)
    (z : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr j.1.root)) :
    edgeCoefficient G.fam (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) G.actual K
        v j d s x z = ∑ α : G.fam.Γ v j, G.physCoeff v j α d.1 s x z := by
  simp only [edgeCoefficient, physicalCoefficient, GenStage.physCoeff, FunLike.coe_sum,
    Finset.sum_apply]

/-- The jets of a classical representative, all orders at once. -/
theorem classicalRepJetsAeAll {K r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (W : TorusHk K E) (a : Vec 2 → E)
    (hW : IsClassicalRep W a r) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ (n : ℕ) (hn : n ≤ r) (word : DerivativeWord2 n),
      W.toFunction.jet ⟨⟨n, Nat.lt_succ_of_le (hn.trans hW.1)⟩, word⟩ x =
        orderedDerivative word a x := by
  have h : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ (hn : n ≤ r)
      (word : DerivativeWord2 n), W.toFunction.jet ⟨⟨n, Nat.lt_succ_of_le (hn.trans hW.1)⟩, word⟩ x =
        orderedDerivative word a x := by
    intro n
    by_cases hn : n ≤ r
    · have h2 : ∀ word : DerivativeWord2 n, ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
          W.toFunction.jet ⟨⟨n, Nat.lt_succ_of_le (hn.trans hW.1)⟩, word⟩ x =
            orderedDerivative word a x := fun word => by
        have h3 := hW.2.2.2 n hn word
        rw [CycleComparison.Coarse.torusJetOrder_of_le W (hn.trans hW.1)] at h3
        exact h3
      filter_upwards [ae_all_iff.2 h2] with x hx _ word using hx word
    · exact Filter.Eventually.of_forall fun x h => absurd h hn
  filter_upwards [ae_all_iff.2 h] with x hx using hx


/-- Almost everywhere in `x`, for all orders and words at once. -/
theorem ae_all_orders {μ : Measure (Vec 2)} {p : ℕ → Prop}
    {Q : ∀ n, p n → DerivativeWord2 n → Vec 2 → Prop}
    (h : ∀ n (hn : p n) (word : DerivativeWord2 n), ∀ᵐ x ∂μ, Q n hn word x) :
    ∀ᵐ x ∂μ, ∀ n (hn : p n) (word : DerivativeWord2 n), Q n hn word x := by
  have h1 : ∀ n : ℕ, ∀ᵐ x ∂μ, ∀ (hn : p n) (word : DerivativeWord2 n), Q n hn word x := by
    intro n
    by_cases hn : p n
    · filter_upwards [ae_all_iff.2 (h n hn)] with x hx _ word using hx word
    · exact Filter.Eventually.of_forall fun x h => absurd h hn
  filter_upwards [ae_all_iff.2 h1] with x hx using hx

/-- A smooth periodic function with the value of `W` is a classical representative of the
truncation of `W` to its order of smoothness. -/
theorem lowRep {K r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] (hrK : r ≤ K)
    (W : TorusHk K E) (a : Vec 2 → E) (hc : ContDiff ℝ (r : ℕ∞) a) (hp : IsZ2Periodic a)
    (hW : W.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] a) :
    IsClassicalRep (truncateTorusHk hrK W) a r :=
  Construction.Preservation.FullLift.classicalRep_of_smooth_periodic_value_ae _ a hc hp hW

/-- The jets of the kernel input are the classical derivatives of the kernel average. -/
theorem flux_jets_ae (G : GenStage D hr Dm b j₀) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (k : ℕ) (v j : CompIn G.comps) (α : G.fam.Γ v j) (s : ℝ) (uhj : Vec 2 → hr j.1.root)
    {Kj : ℕ} (w : TorusHk (Kj + 1) (hr j.1.root))
    (hc : ContDiff ℝ ((Dm - 1 : ℕ) : ℕ∞) uhj) (hp : IsZ2Periodic uhj)
    (hv : w.toFunction.jet (valueIndex2 (Kj + 1)) =ᵐ[volume.restrict AVenhance.unitCube] uhj)
    (y : TorusHk (k + Dm - 1) (hr j.1.root))
    (hy : y.val (valueIndex2 (k + Dm - 1)) =
      G.sysS P seedK freshK φ₀ hφ₀ v j α s (w.val (valueIndex2 (Kj + 1)))) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ (n : ℕ) (hn : n ≤ Kj + 1 ∧ n + 1 ≤ Dm)
      (word : DerivativeWord2 n),
      y.toFunction.jet ⟨⟨n, by omega⟩, word⟩ x =
        orderedDerivative word
          ((G.kernelOf P seedK freshK v j α).applyClassical φ₀ s uhj) x := by
  have hrK : min (Kj + 1) (Dm - 1) ≤ Kj + 1 := min_le_left _ _
  have hrep := lowRep hrK w uhj (hc.of_le (by exact_mod_cast min_le_right _ _)) hp hv
  exact ae_all_orders fun n hn word =>
    Construction.Preservation.Residual.kernel_readout_kernel_lift_jet hφ₀ hφs
      (Providers.hasCompactSupport_of_unitBall hφsupp) (G.kernelOf P seedK freshK v j α) s
      (truncateTorusHk hrK w) y uhj hrep hy (by omega) (by omega) word

/-- The classical derivatives split: `∂(u) = ∂(S u) + ∂(u - S u)`. -/
theorem classical_split_word (G : GenStage D hr Dm b j₀) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (v j : CompIn G.comps) (α : G.fam.Γ v j) (s : ℝ) (uhj : Vec 2 → hr j.1.root) {r n : ℕ}
    (hc : ContDiff ℝ (r : ℕ∞) uhj) (hp : IsZ2Periodic uhj) (hn : n ≤ r)
    (word : DerivativeWord2 n) (x : Vec 2) :
    orderedDerivative word uhj x =
      orderedDerivative word ((G.kernelOf P seedK freshK v j α).applyClassical φ₀ s uhj) x +
      orderedDerivative word (fun y => uhj y -
        (G.kernelOf P seedK freshK v j α).applyClassical φ₀ s uhj y) x := by
  have hS := IterationPassage.Passage.regularKernel_contDiff_periodic hφs hφsupp
    (G.kernelOf P seedK freshK v j α) s hc hp
  have h1 : ContDiff ℝ (n : ℕ∞) uhj := hc.of_le (by exact_mod_cast hn)
  have h2 : ContDiff ℝ (n : ℕ∞) ((G.kernelOf P seedK freshK v j α).applyClassical φ₀ s uhj) :=
    hS.1.of_le (by exact_mod_cast hn)
  rw [orderedDerivative_sub word h1 h2]
  dsimp only
  abel

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
