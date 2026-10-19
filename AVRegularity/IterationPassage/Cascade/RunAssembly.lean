-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.IterationPassage.Cascade.OutputData
import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
import AVRegularity.EntryTerminal.Ingredients.LiftField.LiftField
import AVRegularity.IterationPassage.Passage.Profiles.SmoothRep
import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.EntryTerminal.Ingredients.PrepInterp.PrepInterp
public import AVRegularity.IterationPassage.Passage.StrongEnergyData
import AVRegularity.Proofs.Results.Construction.SuccessorExists
import AVRegularity.Proofs.SeedInvariantDischarge
import AVRegularity.Proofs.Results.Iteration.CascadeSchedule
import AVRegularity.IterationPassage.Cascade.Recursion
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.IterationPassage.Cascade

/-! **The bottom bound of the cascade: statement**.

`CascadeBottomStatement`: above a level `m_B`, a `C^K` periodic representative `a` of an `H^n`
family (`n ≥ K + 2`) on the components of a stage, of marked weighted norm `≤ B` at the enhanced
radius `rhoEnh D cr m` of the passage `m → m-1`, gives the representation `(F a, [])` at the
wavelength `ε_{m-1}` of size `≤ C ε_{m-1}^{-Z_K} B`. The bound is uniform in `m` with the explicit
factor `ε_{m-1}^{-Z_K}`, which is why the constant of the cascade depends on its bottom level.

Special cases. An empty family: `0 ≤ ·`. `B = 0`: the family vanishes almost everywhere, its
continuous periodic representative vanishes, the size is `0`. `a` constant `= c`: the size is the
norm of `c` in normalized coordinates and `B` is at least that, so the bound needs
`C ε^{-Z} ≥ 1`, true for `C ≥ 1`. `n = K + 2`: no truncation. Constants: `C₀, m_B` after
`Λ, K, c_r`, before the data; closed upward in `C`. -/

/-- Data part of the bottom bound: a `C^K` periodic representative of an `H^n` family (`n ≥ K + 2`)
on the retained components of a passage `m → m-1`, of marked weighted norm `≤ B` at the enhanced
radius of the passage, is a representation at the wavelength `ε_{m-1}` with empty list and size
`≤ C ε_{m-1}^{-Z_K} B`. -/
def CascadeBottomData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ K : ℕ) (cr C : ℝ) (mB : ℕ) : Prop :=
  ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
  ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ →
  ∀ (law : BirthLaw), 0 ≤ law.iota →
  ∀ (m : ℕ), mB ≤ m → m ≤ M →
  ∀ {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (Gr : GenStage D ScalarH Dm bw j₀) (n : ℕ), K + 2 ≤ n →
  ∀ (Yn : ∀ v : CompIn Gr.comps, TorusHk n (ScalarH v.1.root))
    (a : Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (B : ℝ),
    ContDiff ℝ (K : ℕ) a → IsZ2Periodic a →
    (∀ v, (Yn v).toFunction.jet (valueIndex2 n) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => a x v) →
    weightedNorm (rhoEnh D cr m) (Gr.mass law) (Gr.marker law) Yn ≤ B →
    representedSize s K (D.eps (m - 1))
        (⟨compField (Gr.mass law) a, []⟩ : Representation (CompSpace Gr.comps)) ≤
      ENNReal.ofReal (C * D.eps (m - 1) ^ (-(iterZ α q s K)) * B)

/-- **The bottom bound**, closed upward in `C`. -/
def CascadeBottomStatement : Prop :=
  ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
  ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ K : ℕ, 1 ≤ K → ∀ cr : ℝ, 0 < cr → cr ≤ 1 →
    ∃ (C₀ : ℝ) (mB : ℕ), ∀ C : ℝ, C₀ ≤ C → CascadeBottomData α s q ζ Λ K cr C mB

end AVRegularity.IterationPassage.Cascade
end

section
open Filter Topology
namespace AVRegularity.IterationPassage.Cascade

/-! **Scale floors, tails and the width exponent of the cascade**.

* `scale_floor`: a positive power of the wavelength, times any constant, is eventually below any
  `η > 0`.
* `scale_sum_tail`: the sums of a positive power of the wavelengths over level intervals above
  level `1` are bounded uniformly in both endpoints (`T = 1/(1 - Λ^{-p})`).
* `cascade_width_exponent_pos`: `δ - 2σ₀ > 0` from the schedule.

The first two restate the private `scaled_power_floor` (`Amplitude/UniformPlan.lean`) and
`scale_sum_le_tail` (`Amplitude/Product.lean`) of the amplitude theorem, whose modules are
dependencies of `cascade_amplitude_product` and are left untouched.

Special cases: `n ≤ j` (empty sum, `0 ≤ T`); `W ≤ 0` (the floor holds from level `0`). Order: `T`
after `(q, Λ, p)`, before `j, n`. -/

/-- A positive power of the wavelength, times any constant, is eventually below `η`. -/
theorem scale_floor {q p W η : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (hp : 0 < p)
    (hη : 0 < η) : ∃ m : ℕ, ∀ j, m ≤ j → W * ocEpsilon q Λ j ^ p ≤ η := by
  have hlim := ((Scales.epsilon_forward_tail (m := 1) hq hΛ le_rfl hp).1.tendsto_atTop_zero).const_mul W
  have hlim' : Tendsto (fun j : ℕ => W * ocEpsilon q Λ (1 + j) ^ p) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim
  obtain ⟨m, hm⟩ := eventually_atTop.mp (hlim' (gt_mem_nhds hη))
  refine ⟨m + 1, ?_⟩
  intro j hj
  have h := hm (j - 1) (by omega)
  dsimp only [Set.mem_ofPred_eq] at h
  simpa only [show 1 + (j - 1) = j by omega] using h.le

/-- The sums of a positive power of the wavelengths over level intervals above level `1`
are bounded uniformly in both endpoints. -/
theorem scale_sum_tail {q : ℝ} {Λ : ℕ} {p : ℝ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (hp : 0 < p) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ j n : ℕ, 1 ≤ j →
      ∑ k ∈ Finset.Ioc j n, ocEpsilon q Λ (k - 1) ^ p ≤ T := by
  have hΛ1 : (1 : ℝ) < Λ := by exact_mod_cast (show 1 < Λ by omega)
  have hden : 0 < 1 - (Λ : ℝ) ^ (-p) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg hΛ1 (neg_lt_zero.mpr hp)
    linarith
  refine ⟨1 / (1 - (Λ : ℝ) ^ (-p)), (div_pos one_pos hden).le, ?_⟩
  intro j n hj
  obtain ⟨hsum, htail⟩ := Scales.epsilon_forward_tail (m := j) hq hΛ hj hp
  have hre : (∑ k ∈ Finset.Ioc j n, ocEpsilon q Λ (k - 1) ^ p) =
      ∑ k ∈ Finset.range (n - j), ocEpsilon q Λ (j + k) ^ p := by
    have hI : Finset.Ioc j n = Finset.Ico (j + 1) (n + 1) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hI, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1; omega) fun k _ => ?_
    congr 2
    omega
  rw [hre]
  have he := Scales.epsilon_basic (m := j) hq hΛ
  have hpow : ocEpsilon q Λ j ^ p ≤ 1 := Real.rpow_le_one he.1.le he.2.1 hp.le
  exact ((hsum.sum_le_tsum _ (fun k _ =>
    Real.rpow_nonneg (Scales.epsilon_basic (m := j + k) hq hΛ).1.le p)).trans htail).trans
      (div_le_div_of_nonneg_right hpow hden.le)

/-- The width exponent of the represented recurrence is positive. -/
theorem cascade_width_exponent_pos {α s q : ℝ} (hα₀ : 0 < α) (hq : IsAdmissibleQ α s q)
    {K : ℕ} {Pacc lamE σE : ℝ} {D₀ : ℕ} {Q : ℝ} {H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ}
    {σ₀ a σ : ℝ}
    (h : IsCascadeSchedule α s q K Pacc lamE σE D₀ Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀
      a σ) : 0 < ocDelta α q - 2 * σ₀ := by
  have hδ := ocDelta_pos_of_admissible hα₀ hq
  obtain ⟨-, -, hsched, -, -, -, -, haσ, hw⟩ := h
  have hσ₀ : σ₀ = a + σ := hsched.2.2.2.2.2.1
  have h3 : 3 * σ < ocDelta α q / (8 * (1 + (succDstar D₀ N p H : ℝ))) :=
    hw.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hD : (1 : ℝ) ≤ 1 + (succDstar D₀ N p H : ℝ) := by
    have : (0 : ℝ) ≤ (succDstar D₀ N p H : ℝ) := Nat.cast_nonneg _
    linarith
  have h8 : ocDelta α q / (8 * (1 + (succDstar D₀ N p H : ℝ))) ≤ ocDelta α q / 8 :=
    div_le_div_of_nonneg_left hδ.le (by norm_num) (by linarith)
  rw [hσ₀]
  linarith

end AVRegularity.IterationPassage.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.IterationPassage.Cascade

/-! **`iteration_cascade_of_schedule` from the run and the families**.

`iteration_cascade_of_schedule_of_ingredients` proves the exact statement
`IterationCascadeOfScheduleStatement` (the text copy of the statement
`iteration_cascade_of_schedule`, `IterationPassage/Assembly/CascadeInterfaces.lean`) from
`CascadeRunStatement` and `CascadeFamiliesStatement` (`Cascade/Statements.lean`). The run chooses the
passage and frame constants `C_pass, C_Q, C_p` and its level threshold; the families are then applied
at these constants and give `C > 0` and their threshold; `m₀` is the maximum of the two.

Special cases: `n = m₀ + 1`; an empty seed family; `f = 0`. -/

/-- **`iteration_cascade_of_schedule` from the run and the families.** -/
theorem iteration_cascade_of_schedule_of_ingredients
    (hrun : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → CascadeRunStatement α s q ζ)
    (hfam : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → CascadeFamiliesStatement α s q ζ) :
    IterationPassage.Assembly.IterationCascadeOfScheduleStatement := by
  classical
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λr, hΛr, hr⟩ := hrun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λf, hΛf, hf⟩ := hfam α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max Λr Λf, by omega, ?_⟩
  intro Λ hΛ
  obtain ⟨cr, hcr, hr⟩ := hr Λ (by omega)
  obtain ⟨cf, hcf, hf⟩ := hf Λ (by omega)
  refine ⟨min cr cf, lt_min hcr hcf, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc t₀ T₀ hK hPacc ht₀ hT₀
    r₀ D₀ τe lamE σE hτe hlamE hσE Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a σ hsched hfloor
    npad
  obtain ⟨SXr, SZr, Kr, hr⟩ := hr φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc t₀
    T₀ hK hPacc ht₀ hT₀ r₀ D₀ τe lamE σE hτe hlamE hσE Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L
    σ₀ a σ hsched hfloor npad
  obtain ⟨SXf, SZf, Kf, hf⟩ := hf φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc t₀
    T₀ hK hPacc ht₀ hT₀ r₀ D₀ τe lamE σE hτe hlamE hσE Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L
    σ₀ a σ hsched npad
  refine ⟨max SXr SXf, max SZr SZf, max Kr Kf, ?_⟩
  intro sX sZ hSX hSZ
  have hr := hr sX sZ ((le_max_left _ _).trans hSX) ((le_max_left _ _).trans hSZ)
  have hf := hf sX sZ ((le_max_right _ _).trans hSX) ((le_max_right _ _).trans hSZ)
  intro Ce kS hCe hc₀ hc₀upper hcr' hcrupper hσf hlamC halloc hKs hKan hLan hJm
  obtain ⟨tr, CHr, Υr, hCHr, hΥr, hr⟩ := hr Ce kS hCe hc₀ (hc₀upper.trans (min_le_left _ _)) hcr'
    hcrupper hσf hlamC halloc ((le_max_left _ _).trans hKs) ((le_max_left _ _).trans hKan)
    ((le_max_left _ _).trans hLan) ((le_max_left _ _).trans hJm)
  obtain ⟨tf', CHf, Υf, hCHf, hΥf, hf⟩ := hf Ce kS hCe hc₀ (hc₀upper.trans (min_le_right _ _)) hcr'
    hcrupper hσf hlamC halloc ((le_max_right _ _).trans hKs) ((le_max_right _ _).trans hKan)
    ((le_max_right _ _).trans hLan) ((le_max_right _ _).trans hJm)
  refine ⟨certificateThresholdJoin tr tf', max CHr CHf, max Υr Υf, hCHr.trans (le_max_left _ _),
    hΥr.trans_le (le_max_left _ _), ?_⟩
  intro kI hkI
  obtain ⟨CIr, Cwr, hr⟩ := hr kI (invariant_admissible_threshold_left hkI)
  obtain ⟨CIf, Cwf, hf⟩ := hf kI (invariant_admissible_threshold_right hkI)
  refine ⟨max CIr CIf, max Cwr Cwf, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hLr : IsLedgerAdmissible Ce CI Cw CIr Cwr :=
    ⟨hledger.1, (le_max_left _ _).trans hledger.2.1, (le_max_left _ _).trans hledger.2.2.1,
      hledger.2.2.2⟩
  have hLf : IsLedgerAdmissible Ce CI Cw CIf Cwf :=
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1, (le_max_right _ _).trans hledger.2.2.1,
      hledger.2.2.2⟩
  have h1 : 1 ≤ Λ := by omega
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos h1) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos h1).le
  have hSr := IsCarrierStart.mono hA hT (le_max_left _ _) (le_max_left _ _)
    (zero_le_one.trans hCHr) hΥr.le hstart
  have hSf := IsCarrierStart.mono hA hT (le_max_right _ _) (le_max_right _ _)
    (zero_le_one.trans hCHf) hΥf.le hstart
  obtain ⟨Cpass, CQ, Cp, mR, hr⟩ := hr CI Cw j₀ hLr hSr
  obtain ⟨mA, hf⟩ := hf CI Cw j₀ hLf hSf Cpass CQ Cp
  obtain ⟨C, hC, hf⟩ := hf (max mR mA) (le_max_right _ _)
  refine ⟨C, CQ, Cp, max mR mA, hC, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
    htS hT₀' hseed hpoint hm₀ hnM
  obtain ⟨stage, ext, hist, st, tp, Preg, hframe, hpass⟩ := hr (max mR mA) (le_max_left _ _) D hDα
    hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf htS hT₀'
    hseed hpoint hm₀ hnM
  exact ⟨stage, ext, hist, st, tp, Preg, hframe, hf D hDα hDq hDΛ
    hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf htS hT₀' hseed
    hpoint hm₀ hnM stage ext hist st tp Preg hframe hpass⟩

end AVRegularity.IterationPassage.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.IterationPassage.Cascade

/-! **The representation of the cascade and its size from the passage data**.


* `passageClauses_step`: the last clause of `PassageClauses` is the step hypothesis of
  `cascade_rep_recursion` (`passageRepAt` is the appended representation by definition).
* `isRepresentationAt_base`: the base `(F aU, [])` is a representation at every wavelength in
  `(0, 1]`.
* `cascade_size_of_parts`: representation, value and size of `rep n` on `I_* = [t_S + t₀, t_f]`
  from `PassageDatum` of every passage at one constant `C₁ ≥ 0` and amplitudes `a_j ≥ 0`, the
  lifts, the representatives, the two defining clauses of `rep`, the bottom bound `X_b` and bounds
  `T_g`, `T_c` of the two sums: `X_n(t) ≤ exp(T_g)(X_b + T_c)`.

Special cases: `n = m₀ + 1`; an empty family (all sizes `0`); `a_j = 0` and `X_b = 0` give
`X_n = 0`. The numbers `C₁, X_b, T_g, T_c` are parameters. -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The last clause of `PassageClauses` is literally the step hypothesis of
`cascade_rep_recursion` (with `g = C(E^{5η₀/4} + E^{μ} + E^{w})`, `c = C E^P A`). -/
theorem passageClauses_step (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth sX sZ K : ℕ) (s η₀ mu wexp P C A tp tf : ℝ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (h : PassageClauses D law G Gr m p N depth sX sZ K s η₀ mu wexp P C A tp tf φ₀ Sr U Y)
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root)
    (haU : ∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => U v t) (aU t) (K + N + 2 * p + 2))
    (haY : ∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) (K + N + 2 * p + 2))
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hCcT : IsPassageLift G m N depth sX sZ CcT) (t : ℝ) (ht : t ∈ Set.Icc tp tf)
    (rY : Representation (CompSpace Gr.comps)) (hrY : IsRepresentationAt (D.eps (m - 1)) K rY)
    (hval : rY.value = compField (Gr.mass law) (aY t)) :
    IsRepresentationAt (D.eps m) K
        ⟨(rY.map (readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law))).base,
          (rY.map (readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law))).profiles ++
            (passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
              fun q => (q.1 t, q.2)⟩ ∧
      (⟨(rY.map (readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law))).base,
          (rY.map (readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law))).profiles ++
            (passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
              fun q => (q.1 t, q.2)⟩ : Representation (CompSpace G.comps)).value =
        compField (G.mass law) (aU t) ∧
      representedSize s K (D.eps m)
          ⟨(rY.map (readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law))).base,
            (rY.map (readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law))).profiles ++
              (passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
                fun q => (q.1 t, q.2)⟩ ≤
        ENNReal.ofReal (1 + C * (D.eps (m - 1) ^ (5 * η₀ / 4) + D.eps (m - 1) ^ mu +
            D.eps (m - 1) ^ wexp)) * representedSize s K (D.eps (m - 1)) rY +
          ENNReal.ofReal (C * D.eps (m - 1) ^ P * A) :=
  (h.2 aU aY haU haY CcT hCcT t ht).2.2.2 rY hrY hval

/-- The base of the recursion is a representation at every wavelength in `(0, 1]`. -/
theorem isRepresentationAt_base {S : Finset Comp} (π : CompIn S → ℝ) {k K n : ℕ} (hKn : K ≤ n)
    (X : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root))
    (a : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) (ha : IsSmoothRep X a n) (e : ℝ)
    (he0 : 0 < e) (he1 : e ≤ 1) :
    IsRepresentationAt e K (⟨compField π a, []⟩ : Representation (CompSpace S)) := by
  obtain ⟨hc, hp, -⟩ := ha
  have h := EntryTerminal.Ingredients.compField_contDiff_periodic π K (fun v x => a x v)
    (fun v => contDiff_pi.mp (hc.of_le (by exact_mod_cast hKn)) v)
    (fun v q x => congrFun (hp q x) v)
  exact ⟨he0, he1, h.1, h.2, by simp⟩

/-- The second half of the per-datum assembly: representation, value and size of `rep n` on
`I_* = [t_S + t₀, t_f]` from the passage data at one constant `C₁` and amplitudes `a_j`, the bottom
bound `X_b` and bounds `T_g`, `T_c` of the two sums. -/
theorem cascade_size_of_parts (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q C₁ cr c₀ : ℝ) (n m₀ : ℕ) (tS t₀ tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (U : (j : ℕ) → ∀ v : CompIn (stage j).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (aU : (j : ℕ) → ℝ → Vec 2 → ∀ v : CompIn (stage j).comps, ScalarH v.1.root)
    (CcT : (j : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage j).comps) (fun v => ScalarH v.1.root))
    (rep : (j : ℕ) → TimeRep (CompSpace (stage j).comps)) (a : ℕ → ℝ)
    (hm : m₀ < n) (hwin : ∀ j, m₀ < j → j ≤ n → tp j ≤ tS + t₀)
    (hε : ∀ k, 0 < D.eps k ∧ D.eps k ≤ 1) (hC₁ : 0 ≤ C₁) (ha : ∀ j, 0 ≤ a j)
    (hdatum : ∀ j, m₀ < j → j ≤ n →
      PassageDatum law P seedK freshK φ₀ hφ₀ (stage j) (stage (j - 1)) j p N depth sX sZ K Naux
        s η₀ mu wexp Pacc Q C₁ cr c₀ (a j) (cascadeRestart D hist st j) (tp j) tf (freshK (j - 1))
        (Preg j) (fun v => U j v (cascadeRestart D hist st j)) (U j) (U (j - 1)))
    (hlift : ∀ j, m₀ < j → j ≤ n → IsPassageLift (stage j) j N depth sX sZ (CcT j))
    (hreps : ∀ j, m₀ < j → j ≤ n → ∀ t ∈ Set.Icc (tp j) tf,
      IsSmoothRep (fun v => U j v t) (aU j t) (K + N + 2 * p + 2) ∧
      IsSmoothRep (fun v => U (j - 1) v t) (aU (j - 1) t) (K + N + 2 * p + 2))
    (hrec : ∀ j, m₀ < j → j ≤ n →
      rep j = ((rep (j - 1)).map (readoutCLM j (D.eps (j - 1)) η₀ ((stage j).mass law)
          ((stage (j - 1)).mass law))).append
        (passageProfiles D law (stage j) (stage (j - 1)) j p N depth η₀ φ₀ (freshK (j - 1))
          (CcT j) (aU j) (aU (j - 1))))
    (hbase : rep m₀ = ⟨fun t => compField ((stage m₀).mass law) (aU m₀ t), []⟩)
    (Xb Tg Tc : ℝ) (hXb : 0 ≤ Xb)
    (hbot : ∀ t ∈ Set.Icc (tS + t₀) tf, representedSize s K (D.eps m₀)
      (⟨compField ((stage m₀).mass law) (aU m₀ t), []⟩ :
        Representation (CompSpace (stage m₀).comps)) ≤ ENNReal.ofReal Xb)
    (hTg : ∑ j ∈ Finset.Ioc m₀ n, C₁ * (D.eps (j - 1) ^ (5 * η₀ / 4) + D.eps (j - 1) ^ mu +
      D.eps (j - 1) ^ wexp) ≤ Tg)
    (hTc : ∑ j ∈ Finset.Ioc m₀ n, C₁ * D.eps (j - 1) ^ Pacc * a j ≤ Tc) :
    ∀ t ∈ Set.Icc (tS + t₀) tf,
      IsRepresentationAt (D.eps n) K ((rep n).atTime t) ∧
      ((rep n).atTime t).value = compField ((stage n).mass law) (aU n t) ∧
      representedSize s K (D.eps n) ((rep n).atTime t) ≤
        ENNReal.ofReal (Real.exp Tg * (Xb + Tc)) := by
  intro t ht
  have hge : ∀ j, 0 ≤ C₁ * (D.eps (j - 1) ^ (5 * η₀ / 4) + D.eps (j - 1) ^ mu +
      D.eps (j - 1) ^ wexp) := fun j => mul_nonneg hC₁ (add_nonneg (add_nonneg
    (Real.rpow_nonneg (hε _).1.le _) (Real.rpow_nonneg (hε _).1.le _))
    (Real.rpow_nonneg (hε _).1.le _))
  have hce : ∀ j, 0 ≤ C₁ * D.eps (j - 1) ^ Pacc * a j := fun j =>
    mul_nonneg (mul_nonneg hC₁ (Real.rpow_nonneg (hε _).1.le _)) (ha j)
  have hrep0 : ∀ t, (rep m₀).atTime t =
      (⟨compField ((stage m₀).mass law) (aU m₀ t), []⟩ :
        Representation (CompSpace (stage m₀).comps)) := by
    intro t
    rw [hbase]
    rfl
  obtain ⟨h1, h2, h3⟩ := cascade_rep_recursion (H := fun j => CompSpace (stage j).comps) s K m₀ n
    hm.le D.eps (Set.Icc (tS + t₀) tf)
    (fun j => readoutCLM (j + 1) (D.eps j) η₀ ((stage (j + 1)).mass law) ((stage j).mass law))
    (fun j => passageProfiles D law (stage (j + 1)) (stage j) (j + 1) p N depth η₀ φ₀ (freshK j)
      (CcT (j + 1)) (aU (j + 1)) (aU j))
    rep (fun j t => compField ((stage j).mass law) (aU j t))
    (fun j => C₁ * (D.eps (j - 1) ^ (5 * η₀ / 4) + D.eps (j - 1) ^ mu + D.eps (j - 1) ^ wexp))
    (fun j => C₁ * D.eps (j - 1) ^ Pacc * a j) hge hce
    (fun t ht => by
      have hsm := (hreps (m₀ + 1) (Nat.lt_succ_self _) hm t
        ⟨(hwin (m₀ + 1) (Nat.lt_succ_self _) hm).trans ht.1, ht.2⟩).2
      rw [hrep0 t]
      refine ⟨isRepresentationAt_base _ (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _)
        |>.trans (Nat.le_add_right _ _)) _ _ hsm _ (hε m₀).1 (hε m₀).2, ?_⟩
      funext x
      simp [Representation.value])
    (fun j hj hjn => hrec (j + 1) (Nat.lt_succ_of_le hj) hjn)
    (fun j hj hjn t ht rY hrY hval =>
      passageClauses_step law (stage (j + 1)) (stage j) (j + 1) p N depth sX sZ K s η₀ mu wexp
        Pacc C₁ (a (j + 1)) (tp (j + 1)) tf φ₀ (freshK j) (U (j + 1)) (U j)
        (hdatum (j + 1) (Nat.lt_succ_of_le hj) hjn).2.2.1 (aU (j + 1)) (aU j)
        (fun t ht => (hreps (j + 1) (Nat.lt_succ_of_le hj) hjn t ht).1)
        (fun t ht => (hreps (j + 1) (Nat.lt_succ_of_le hj) hjn t ht).2)
        (CcT (j + 1)) (hlift (j + 1) (Nat.lt_succ_of_le hj) hjn) t
        ⟨(hwin (j + 1) (Nat.lt_succ_of_le hj) hjn).trans ht.1, ht.2⟩ rY hrY hval) t ht
  refine ⟨h1, h2, h3.trans ?_⟩
  rw [hrep0 t]
  have hTc0 : 0 ≤ Tc := (Finset.sum_nonneg fun j _ => hce j).trans hTc
  calc _ ≤ ENNReal.ofReal (Real.exp Tg) * (ENNReal.ofReal Xb + ENNReal.ofReal Tc) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hTg))
          (add_le_add (hbot t ht) (ENNReal.ofReal_le_ofReal hTc))
    _ = ENNReal.ofReal (Real.exp Tg * (Xb + Tc)) := by
        rw [← ENNReal.ofReal_add hXb hTc0, ← ENNReal.ofReal_mul (Real.exp_pos _).le]

end AVRegularity.IterationPassage.Cascade
end

section
namespace AVRegularity.IterationPassage.Cascade

/-! **The bottom bound of the cascade**:
`cascadeBottom : CascadeBottomStatement`.

Route: the enhanced radius `ρ = c_r · ocRh` is `≍ E^{1+c}` (`bandChain_renewal_radius`) and `≤ 1`
above `m_B` (`scale_floor`); the unmarked norm of the truncation to order `K+2` is at most the
marked norm (`compMarker_one_le`, `weightedNorm_truncate_le`); `sobolevProfile` bounds the profile
norm; `bottom_scale_sum_le` turns `∑_j E^{j-s}ρ^{-j-1}` into `E^{-Z_K}`; the represented size is
at most `4` times the profile norm. `C₀ = 4 C_K (K+1) (C_r/c_r)^{K+1}`. -/

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity AVenhance
open AVRegularity.IterationPassage.Passage
open scoped ENNReal

theorem cascadeBottom : CascadeBottomStatement := by
  intro α s hα0 hα1 hs0 hs1 q hq ζ hζ
  obtain ⟨Cr, hCr1, Λr, hΛr, hband⟩ :=
    CycleReference.bandChain_renewal_radius hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λr, hΛr, ?_⟩
  intro Λ hΛ K hK cr hcr0 hcr1
  have hΛ128 : 128 ≤ Λ := hΛr.trans hΛ
  have hq1 : 1 < q := hq.1
  have hc : 0 < ocC α q := ocC_pos_of_admissible hα0 hq
  obtain ⟨m1, hm1⟩ := scale_floor (W := Cr) (η := 1) (p := 1 + ocC α q) hq1 hΛ128
    (by linarith) one_pos
  obtain ⟨CK, hCK0, hSob⟩ := sobolevProfile K
  have hCr0 : 0 < Cr := by linarith
  refine ⟨4 * CK * ((K : ℝ) + 1) * (Cr / cr) ^ (K + 1), max (m1 + 1) 2, ?_⟩
  intro C hC D hDα hDq hDΛ hDζ M hbc law hiota m hm hmM Dm bw j₀ Gr n hn Yn a B hCd hper hX hB
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hm1' : m1 ≤ m - 1 := by have := (le_max_left _ _).trans hm; omega
  set E : ℝ := D.eps (m - 1) with hEdef
  have hE : E = ocEpsilon q Λ (m - 1) := by rw [hEdef, OCData.eps, hDq, hDΛ]
  obtain ⟨hE0, hE1, -⟩ := Scales.epsilon_basic (m := m - 1) hq1 hΛ128
  rw [← hE] at hE0 hE1
  have hrad := hband Λ hΛ M (by omega) D.κ hbc m hm2 hmM
  rw [← hE] at hrad
  have hfloor : Cr * E ^ (1 + ocC α q) ≤ 1 := by
    have := hm1 (m - 1) hm1'
    rwa [← hE] at this
  have hρeq : rhoEnh D cr m = cr * ocRh α q Λ m (D.κ (m - 1)) := by
    unfold rhoEnh ocRh
    rw [hDα, hDq, hDΛ]
  have hlow : cr / Cr * E ^ (1 + ocC α q) ≤ rhoEnh D cr m := by
    rw [hρeq]
    have := hrad.1
    calc cr / Cr * E ^ (1 + ocC α q) = cr * (Cr⁻¹ * E ^ (1 + ocC α q)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hcr0.le
  have hρ0 : 0 < rhoEnh D cr m := lt_of_lt_of_le (by positivity) hlow
  have hρ1 : rhoEnh D cr m ≤ 1 := by
    rw [hρeq]
    have h1 := hrad.2
    have h2 : ocRh α q Λ m (D.κ (m - 1)) ≤ 1 := h1.trans hfloor
    nlinarith [Real.sqrt_nonneg (D.κ (m - 1) * ocTauPP α q Λ m)]
  -- masses and markers
  have hmass : ∀ v, 0 < Gr.mass law v := by
    intro v
    unfold GenStage.mass
    exact Construction.Preservation.Buffer.birth_compMass_pos (by rw [hDq]; exact hq1)
      (by rw [hDΛ]; exact hΛ128) law v.1
  have hmark : ∀ v, 1 ≤ Gr.marker law v := by
    intro v
    unfold GenStage.marker
    exact Construction.Preservation.FullLift.compMarker_one_le (by rw [hDq]; exact hq1)
      (by rw [hDΛ]; exact hΛ128) law hiota v.1
  -- truncation
  have hKn : K + 2 ≤ n := hn
  let X : ∀ v : CompIn Gr.comps, TorusHk (K + 2) (ScalarH v.1.root) :=
    fun v => truncateTorusHk hKn (Yn v)
  have hXa : ∀ v, (X v).toFunction.jet (valueIndex2 (K + 2)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => a x v := fun v =>
    (AVRegularity.IterationPassage.torus_truncate_value_ae hKn (Yn v)).trans (hX v)
  have hW : weightedNorm (rhoEnh D cr m) (Gr.mass law) (fun _ => 1) X ≤ B :=
    calc _ ≤ weightedNorm (rhoEnh D cr m) (Gr.mass law) (fun _ => 1) Yn :=
          EntryTerminal.Ingredients.weightedNorm_truncate_le hKn _ _ hmass Yn
      _ ≤ weightedNorm (rhoEnh D cr m) (Gr.mass law) (Gr.marker law) Yn :=
          bottom_weightedNorm_le_marked _ _ _ hmass hmark Yn
      _ ≤ B := hB
  have hW0 : 0 ≤ weightedNorm (rhoEnh D cr m) (Gr.mass law) (fun _ => 1) X := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := hW0.trans hW
  -- the field
  have hFC : ContDiff ℝ (K : ℕ) (compField (Gr.mass law) a) := by
    have hpi : ContDiff ℝ (K : ℕ) (fun x => fun v : CompIn Gr.comps =>
        (Real.sqrt (Gr.mass law v))⁻¹ * a x v) :=
      contDiff_pi.mpr fun v => contDiff_const.mul (contDiff_pi.mp hCd v)
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : CompIn Gr.comps => ℝ)).symm.contDiff.comp hpi
  have hFP : IsZ2Periodic (compField (Gr.mass law) a) := by
    intro p x
    show toCompSpace (Gr.mass law) (a (x + latticeShift p)) = toCompSpace (Gr.mass law) (a x)
    rw [hper p x]
  have hprof := hSob (Gr.mass law) hmass (rhoEnh D cr m) E s hρ0 hρ1 hE0 X a hFC hFP hXa
  have hsize := bottom_representedSize_le (s := s) (lam := E) hK hE0 hE1 hs0
    (by linarith) (compField (Gr.mass law) a) hFC hFP
  have hT := bottom_scale_sum_le (E := E) (ρ := rhoEnh D cr m) (cr := cr) (Cr := Cr)
    (c := ocC α q) (s := s) (K := K) hE0 hE1 hcr0 hCr1 hcr1 hc.le hlow
  set W := weightedNorm (rhoEnh D cr m) (Gr.mass law) (fun _ => 1) X with hWdef
  have hEZ : 0 ≤ E ^ (-(iterZ α q s K)) := (Real.rpow_pos_of_pos hE0 _).le
  have hCnn : 0 ≤ 4 * CK * ((K : ℝ) + 1) * (Cr / cr) ^ (K + 1) := by positivity
  have hnum : 4 * (CK * (∑ j ∈ Finset.range (K + 1),
        E ^ ((j : ℝ) - s) * (rhoEnh D cr m) ^ (-(j : ℝ) - 1)) * W) ≤
      C * E ^ (-(iterZ α q s K)) * B := by
    have hZ : iterZ α q s K = 1 + s + ocC α q * ((K : ℝ) + 1) := rfl
    rw [hZ]
    have hT0 : 0 ≤ ∑ j ∈ Finset.range (K + 1),
        E ^ ((j : ℝ) - s) * (rhoEnh D cr m) ^ (-(j : ℝ) - 1) :=
      Finset.sum_nonneg fun j _ => by positivity
    calc 4 * (CK * (∑ j ∈ Finset.range (K + 1),
          E ^ ((j : ℝ) - s) * (rhoEnh D cr m) ^ (-(j : ℝ) - 1)) * W)
        ≤ 4 * (CK * (((K : ℝ) + 1) * ((Cr / cr) ^ (K + 1) *
            E ^ (-(1 + s + ocC α q * ((K : ℝ) + 1))))) * B) := by
          gcongr
      _ = (4 * CK * ((K : ℝ) + 1) * (Cr / cr) ^ (K + 1)) *
            E ^ (-(1 + s + ocC α q * ((K : ℝ) + 1))) * B := by ring
      _ ≤ C * E ^ (-(1 + s + ocC α q * ((K : ℝ) + 1))) * B := by
          rw [hZ] at hEZ
          gcongr
  calc _ ≤ 4 * profileNorm E K s (compField (Gr.mass law) a) := hsize
    _ ≤ 4 * ENNReal.ofReal (CK * (∑ j ∈ Finset.range (K + 1),
          E ^ ((j : ℝ) - s) * (rhoEnh D cr m) ^ (-(j : ℝ) - 1)) * W) := by gcongr
    _ = ENNReal.ofReal (4 * (CK * (∑ j ∈ Finset.range (K + 1),
          E ^ ((j : ℝ) - s) * (rhoEnh D cr m) ^ (-(j : ℝ) - 1)) * W)) := by
        rw [ENNReal.ofReal_mul (p := 4) (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hnum

end AVRegularity.IterationPassage.Cascade
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.Cascade

/-! **Inputs of the run of the cascade with their data parts named**.

The statements `successor_exists` and `seed_invariant_discharge` with the part after the
level threshold named (`SuccessorExistsData`, `SeedInvariantData`); `successorExistsSplit` and
`seedInvariantSplit` are their proofs (definitional unfolding). The statements are text
copies of `successor_exists` and `seed_invariant_discharge`. -/

/-- The data part of `successor_exists`. -/
def SuccessorExistsData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk npad sX sZ : ℕ) (σ₀ : ℝ) (kI : InvConsts)
    (CI Cw : ℝ) (j₀ mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ G : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀,
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      (∃ tA : ℝ, tS ≤ tA ∧
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G) →
      ∃ G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀,
        IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
          (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G'

/-- `successor_exists` with its data part named. -/
def SuccessorExistsSplit : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ mStar : ℕ,
    SuccessorExistsData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI Cw j₀ mStar

/-- The statement `successor_exists`. -/
theorem successorExistsSplit : SuccessorExistsSplit := Providers.successor_exists

/-- The data part of `seed_invariant_discharge`. -/
def SeedInvariantData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk npad : ℕ) (σ₀ : ℝ) (kI : InvConsts)
    (CI Cw : ℝ) (j₀ mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      mStar ≤ n → n < M →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tS tf (CI * D.eps n ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (n - 1) ^ (q * min (ocDelta α q / 4) τe)) seed

/-- `seed_invariant_discharge` with its data part named. -/
def SeedInvariantSplit : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad _sX _sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ mStar : ℕ,
    SeedInvariantData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad σ₀ kI CI Cw j₀ mStar

/-- The statement `seed_invariant_discharge`. -/
theorem seedInvariantSplit : SeedInvariantSplit := Providers.seed_invariant_discharge

/-- `IterationPassageStatement` in its split form. -/
theorem iterationPassageSplit_of_statement
    (h : IterationPassage.Assembly.IterationPassageStatement) :
    Passage.IterationPassageSplit := h

/-! **The run of the cascade at the data**.

`cascadeRunData_of_parts`: the data part `CascadeRunData` of `CascadeRunStatement` from the data
parts of `iteration_passage`, `successor_exists`, `seed_invariant_discharge` and the wait bound of
`cascade_wait`, for a bottom level `m₀` above their thresholds. It instantiates the abstract
recursion `exists_cascade_run` (`Cascade/Recursion.lean`):

* the seed has level `n` (`IsGeneratedSeed`), is a cascade stage and satisfies the invariant on
  `[t_S, t_f]` (`seed_invariant_discharge`);
* at a level `m₀ < j ≤ n` the stage has an actual successor (`successor_exists`) and the passage
  `j → j - 1` from `t_A = a_j`, `s₀ = r_j = max{s_j, a_j + 3τ_j}` gives the frame and the output
  (`iteration_passage`); the frame gives `r_j ≤ t_p ≤ r_j + 4τ_j''` (`IsCommonPreparation`), the
  cascade stage and the invariant of the retained stage;
* the passage constant serves as the frame constant `C_p`.

Special cases: `n = m₀ + 1` (one passage); an empty seed family (nothing changes: the run is
datum-independent). -/

/-- The type of the preparations of a stage. -/
def PrepType {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (Nout : ℕ)
    (G : GenStage D ScalarH Dm b j₀) : Type :=
  (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
    (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))

instance {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (Nout : ℕ) (G : GenStage D ScalarH Dm b j₀) :
    Nonempty (PrepType Nout G) :=
  ⟨(0 : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
    (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root)))⟩

/-- The data part of the run of the cascade. -/
theorem cascadeRunData_of_parts {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : Integrable φ₀} {bw : ℝ} {K : ℕ} {Pacc t₀ T₀ : ℝ} {r₀ D₀ : ℕ} {τe Q : ℝ}
    {H J N p nk Naux Nout Kres npad sX sZ : ℕ} {σ₀ Ce : ℝ} {kS kI : InvConsts} {CI Cw : ℝ}
    {j₀ : ℕ} (hΛ : 1 ≤ Λ) (C CQ : ℝ) (mP mS mI m₀ : ℕ) (hmP : mP ≤ m₀) (hmS : mS ≤ m₀)
    (hmI : mI ≤ m₀)
    (hpass : Passage.IterationPassageData α s q ζ Λ φ₀ hφ₀ bw K Pacc Q T₀ r₀ D₀ τe H J N p nk Naux
      Nout Kres npad σ₀ sX sZ Ce kS kI CI Cw j₀ C CQ mP)
    (hsucc : SuccessorExistsData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI
      Cw j₀ mS)
    (hseed : SeedInvariantData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad σ₀ kI CI Cw j₀
      mI)
    (hwait : ∀ n : ℕ, ∑ j ∈ Finset.Ioc m₀ n, (3 * ocTau α q Λ j + 4 * ocTauPP α q Λ j) < t₀) :
    CascadeRunData α s q ζ Λ φ₀ hφ₀ bw K Pacc t₀ T₀ r₀ D₀ τe Q H J N p nk Naux Nout Kres npad sX
      sZ σ₀ Ce kS kI CI Cw j₀ C CQ C m₀ := by
  intro D hα hq hΛ' hζ
  subst hα hq hΛ' hζ
  intro hΦ M hκ hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf ht₀ hT₀ hgen hmol hm₀n
    hnM
  have hpass' := hpass D rfl rfl rfl rfl hΦ M hκ hterm Mnat hMnat law hlaw seedK freshK hfresh
    seed n tS tf hgen hmol
  have hsucc' := hsucc D rfl rfl rfl rfl hΦ M hκ hterm Mnat hMnat law hlaw (hr := ScalarH) seedK
    freshK hfresh seed n tS tf hgen
  have hseed' := hseed D rfl rfl rfl rfl hΦ M hκ hterm Mnat hMnat law hlaw (hr := ScalarH) seedK
    freshK hfresh seed n tS tf hgen (hmI.trans hm₀n.le) hnM
  obtain ⟨stage, ext, hist, st, tp, Preg, h1, h2, h3, h4, hA, hB⟩ := exists_cascade_run
    (Stg := GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀)
    (PrepT := PrepType Nout)
    (fun G => G.level)
    (fun G => IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 D.α D.q s) N p)
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 D.α D.q s)) seed G)
    (fun j tA G => IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 D.α D.q s) N p)
      seedK freshK φ₀ hφ₀ Mnat kI tA tf (CI * D.eps j ^ min (ocDelta D.α D.q / 4) τe)
      (CI * D.eps (j - 1) ^ (D.q * min (ocDelta D.α D.q / 4) τe)) G)
    (fun G G' => IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 D.α D.q s) N p)
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 D.α D.q s)) G G')
    (fun j G' => G'.retained j H J)
    (fun G Gr j tA s₀ tp Preg => PassageFrame law
      (succProvParams D Cw kI.cr σ₀ (succEta0 D.α D.q s) N p)
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 D.α D.q s)) seedK freshK φ₀ hφ₀ Mnat kI CI
      τe seed G Gr j (succEta0 D.α D.q s) Kres
      (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card p Nout Naux Q CQ C tA s₀ tf
      tp Preg)
    (fun G Gr j s₀ tp Preg => PassageOutput law
      (succProvParams D Cw kI.cr σ₀ (succEta0 D.α D.q s) N p) seedK freshK φ₀ hφ₀ G Gr j p N
      (succSchedR r₀ J H) sX sZ K Naux s (succEta0 D.α D.q s) (ocMuS D.α D.q s)
      (ocDelta D.α D.q - 2 * σ₀) Pacc Q C kI.cr kI.c₀ s₀ tp tf (freshK (j - 1)) Preg)
    (ocTau D.α D.q D.Λ) (ocTauPP D.α D.q D.Λ)
    (fun _ => (Construction.Stream.ocTau_pos hΛ).le)
    (fun _ => (Construction.Stream.ocTauPP_pos hΛ).le)
    seed n m₀ tS t₀ tf T₀ hm₀n (hwait n) ht₀ hT₀ hgen.1 IsCascadeStage.seed hseed'
    (fun j G tA hj hjn hc hlev htA hiv =>
      hsucc' j (hmS.trans hj.le) hjn hnM G hc hlev ⟨tA, htA, hiv⟩)
    (fun j G G' tA s₀ hj hjn htA hs₀ hwin hT hc hlev hiv hsuc =>
      hpass' j (hmP.trans hj.le) hjn hnM tA s₀ htA hs₀ hwin hT G G' hc hlev hiv hsuc)
    (fun j G Gr tA s₀ tp Preg hlev hF =>
      ⟨hF.1.2.1, by simpa only [hlev] using hF.1.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2.1⟩)
    (fun j G G' hlev hsuc => by
      show G'.level = j - 1
      rw [hsuc.2.1, hlev])
  refine ⟨stage, ext, hist, st, tp, Preg, ⟨h1, h2, h3, h4, hA, fun j hj hjn => ?_⟩,
    fun j hj hjn => (hB j hj hjn).2.2.2.2.2.2⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := hB j hj hjn
  exact ⟨b1, b2, b3, b4, b5, b6⟩

end AVRegularity.IterationPassage.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.IterationPassage.Cascade

/-! **The run of the cascade from `iteration_passage`**.

`cascadeRunStatement_of_passage` proves `CascadeRunStatement` from the statement
`IterationPassageStatement` (the text copy of the statement `iteration_passage`) and
`successor_exists`, `seed_invariant_discharge`, `cascade_wait`, which are applied
directly. `iteration_cascade_of_schedule_of_passage` is then the statement
`iteration_cascade_of_schedule` from `iteration_passage` and `CascadeFamiliesStatement`.

Quantifier alignment. The schedule block `IsCascadeSchedule` gives the premises of the passage
(`Q > 0`, `Q/2 > P + qZ_K + 4`, the successor schedule, the orders and the widths); `T₀ > 0` from
`0 < t₀ < T₀`. Lift floors: the maximum of the floor of the passage and the explicit floor
`max (N + D_H) (2p) + D_{H+1} + 2` of `successor_exists`. `Λ₀` by maxima, `c₀max` by minima, the
thresholds by `certificateThresholdJoin`, carrier constants and ledger thresholds by maxima. The
passage constants `C, C_Q` serve as `C_pass = C_p = C` and `C_Q`; the bottom level `m₀` is any
level above the thresholds of the passage, of `successor_exists`, of `seed_invariant_discharge`
and of the wait `cascade_wait` at `t₀`.

Special cases: `n = m₀ + 1`; the seed alone is excluded by `m₀ < n`. -/

/-- **The run of the cascade** from `iteration_passage` and the producers. -/
theorem cascadeRunStatement_of_passage
    (hip : IterationPassage.Assembly.IterationPassageStatement) (α s : ℝ) (hα₀ : 0 < α)
    (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : CascadeRunStatement α s q ζ := by
  classical
  obtain ⟨Λp, hΛp, hp⟩ := iterationPassageSplit_of_statement hip α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λe, hΛe, he⟩ := successorExistsSplit α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λi, hΛi, hi⟩ := seedInvariantSplit α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λw, hΛw, hw⟩ := Providers.cascade_wait α s hα₀ hα₁ hs₀ hs₁ q hq
  refine ⟨max (max Λp Λe) (max Λi Λw), by omega, ?_⟩
  intro Λ hΛ
  have h1 : 1 ≤ Λ := by omega
  obtain ⟨cp, hcp, hp⟩ := hp Λ (by omega)
  obtain ⟨ce, hce, he⟩ := he Λ (by omega)
  obtain ⟨ci, hci, hi⟩ := hi Λ (by omega)
  have hw := hw Λ (by omega)
  refine ⟨min (min cp ce) ci, lt_min (lt_min hcp hce) hci, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc t₀ T₀ hK hPacc ht₀ hT₀
    r₀ D₀ τe lamE σE hτe hlamE hσE Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a σ hsched hfloor
    npad
  obtain ⟨hQ, hPQ, hss, hNaux, hNout, horders, hwidths⟩ := hsched
  have hT₀pos : 0 < T₀ := ht₀.trans hT₀
  obtain ⟨SXp, SZp, Kp, hp⟩ := hp φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK
    hPacc Q T₀ hQ hT₀pos hPQ r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres
    npad σ₀ a σ hss hNaux hNout hfloor L horders hwidths
  refine ⟨max SXp (max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2),
    max SZp (max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2), Kp, ?_⟩
  intro sX sZ hSX hSZ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf hlamC halloc hKs hKan hLan hJm
  have hσf' : 0 < kS.σf := hσf.symm ▸ hσE
  have hlamC' : 0 < kS.lamC := hlamC.symm ▸ hlamE
  have hss' : IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N
      p nk Lc Lf Lpr Acl Naux Nout := by
    simpa only [hσf, hlamC] using hss
  obtain ⟨tp, CHp, Υp, hCHp, hΥp, hp⟩ := hp sX sZ ((le_max_left _ _).trans hSX)
    ((le_max_left _ _).trans hSZ) Ce kS hCe hc₀
    (hc₀upper.trans ((min_le_left _ _).trans (min_le_left _ _))) hcr hcrupper hσf hlamC halloc
    hKs hKan hLan hJm
  obtain ⟨te, CHe, Υe, hCHe, hΥe, he⟩ := he φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀pos Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans ((min_le_left _ _).trans (min_le_right _ _))) hcr hcrupper hσf' hlamC'
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hss' hNaux hNout halloc
    ((le_max_right _ _).trans hSX) ((le_max_right _ _).trans hSZ)
  obtain ⟨ti, CHi, Υi, hCHi, hΥi, hi⟩ := hi φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀pos Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_right _ _)) hcr hcrupper
    hσf' hlamC' H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hss' hNaux hNout halloc
  refine ⟨certificateThresholdJoin (certificateThresholdJoin tp te) ti,
    max (max CHp CHe) CHi, max (max Υp Υe) Υi,
    hCHp.trans ((le_max_left _ _).trans (le_max_left _ _)),
    hΥp.trans_le ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro kI hkI
  have hk1 := invariant_admissible_threshold_left hkI
  obtain ⟨CIp, Cwp, hp⟩ := hp kI (invariant_admissible_threshold_left hk1)
  obtain ⟨CIe, Cwe, he⟩ := he kI (invariant_admissible_threshold_right hk1)
  obtain ⟨CIi, Cwi, hi⟩ := hi kI (invariant_admissible_threshold_right hkI)
  refine ⟨max (max CIp CIe) CIi, max (max Cwp Cwe) Cwi, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hLp : IsLedgerAdmissible Ce CI Cw CIp Cwp :=
    ⟨hledger.1, ((le_max_left _ _).trans (le_max_left _ _)).trans hledger.2.1,
      ((le_max_left _ _).trans (le_max_left _ _)).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLe : IsLedgerAdmissible Ce CI Cw CIe Cwe :=
    ⟨hledger.1, ((le_max_right _ _).trans (le_max_left _ _)).trans hledger.2.1,
      ((le_max_right _ _).trans (le_max_left _ _)).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLi : IsLedgerAdmissible Ce CI Cw CIi Cwi :=
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1, (le_max_right _ _).trans hledger.2.2.1,
      hledger.2.2.2⟩
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos h1) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos h1).le
  have hSp := IsCarrierStart.mono hA hT ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_left _ _).trans (le_max_left _ _)) (zero_le_one.trans hCHp) hΥp.le hstart
  have hSe := IsCarrierStart.mono hA hT ((le_max_right _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _)) (zero_le_one.trans hCHe) hΥe.le hstart
  have hSi := IsCarrierStart.mono hA hT (le_max_right _ _) (le_max_right _ _)
    (zero_le_one.trans hCHi) hΥi.le hstart
  obtain ⟨C, CQ, mP, hp⟩ := hp CI Cw j₀ hLp hSp
  obtain ⟨mS, he⟩ := he CI Cw j₀ hLe hSe
  obtain ⟨mI, hi⟩ := hi CI Cw j₀ hLi hSi
  obtain ⟨m₁, hw⟩ := hw t₀ ht₀
  refine ⟨C, CQ, C, max (max mP mS) (max mI m₁), ?_⟩
  intro m₀ hm₀
  exact cascadeRunData_of_parts h1 C CQ mP mS mI m₀
    (((le_max_left _ _).trans (le_max_left _ _)).trans hm₀)
    (((le_max_right _ _).trans (le_max_left _ _)).trans hm₀)
    (((le_max_left _ _).trans (le_max_right _ _)).trans hm₀) hp he hi
    (hw m₀ (((le_max_right _ _).trans (le_max_right _ _)).trans hm₀))

/-- **`iteration_cascade_of_schedule` from `iteration_passage` and the families of the
cascade.** -/
theorem iteration_cascade_of_schedule_of_passage
    (hip : IterationPassage.Assembly.IterationPassageStatement)
    (hfam : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → CascadeFamiliesStatement α s q ζ) :
    IterationPassage.Assembly.IterationCascadeOfScheduleStatement :=
  iteration_cascade_of_schedule_of_ingredients
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
      cascadeRunStatement_of_passage hip α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ) hfam

end AVRegularity.IterationPassage.Cascade
end
end
end
