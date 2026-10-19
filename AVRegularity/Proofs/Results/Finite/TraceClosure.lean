-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep
import AVRegularity.EntryWeak.JointSourceCongruence
public import AVRegularity.Definitions.Construction.DiagLetter
import AVRegularity.Construction.EntryScales.TerminalCore
public import AVRegularity.Proofs.Results.Finite.TraceClosure.TestSeparation
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVRegularity.CoupledEnergy.Galerkin.CarrierFamilyProjection
public import AVRegularity.Statements.Construction.IsAdmissibleQ
import AVRegularity.Applications.Torus.JointContinuityMain
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers

/-! Proof of `torusHk_classicalRep_exists` (`H^{r+2}(𝕋²) ⊂ C^r`).

The representative is the real part of the Fourier series of the value class
(`EntryWeakProofs.realClassicalLift`), which is `C^r`, `ℤ²`-periodic, and a.e. equal to the value
class when `r + 2 ≤ K` (two reserved derivatives make the coefficients absolutely summable with
`r` polynomial weights). Its classical ordered jet through order `r` is a periodic weak jet
(`classicalFiniteHk`), so the promoted `TorusHk r` element has the value class of the truncation of
`W`; by uniqueness of weak derivatives (`TorusHk.ext_value`) the two elements coincide, and the
classical ordered derivatives are a.e. the weak jets. -/

/-- The ordered derivative `orderedDerivative` is the classical word derivative of the reversed
word. -/
theorem orderedDerivative_eq_classicalWordDerivative :
    ∀ {m : ℕ} (w : DerivativeWord2 m) (g : Vec 2 → ℝ),
      orderedDerivative w g =
        AVenhance.Infra.Classical.classicalWordDerivative
          (AVRegularity.CoupledEnergy.Galerkin.smoothLiftWord m w) g
  | 0, w, g => by
      simp [orderedDerivative, AVRegularity.CoupledEnergy.Galerkin.smoothLiftWord,
        AVenhance.Infra.Classical.classicalWordDerivative]
  | m + 1, w, g => by
      have ih := orderedDerivative_eq_classicalWordDerivative (Fin.init w) g
      have hsnoc : orderedDerivative w g =
          fun x => fderiv ℝ (orderedDerivative (Fin.init w) g) x (basisVec (w (Fin.last m))) := by
        conv_lhs => rw [← Fin.snoc_init_self w]
        simp only [orderedDerivative, List.ofFn_succ', List.concat_eq_append, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hsnoc, ih]
      rfl

/-- **Classical representatives exist** (Sobolev embedding `H^{r+2}(𝕋²) ⊂ C^r`). -/
theorem torusHk_classicalRep_exists (K r : ℕ) (h : r + 2 ≤ K) (W : TorusHk K ℝ) :
    ∃ a : Vec 2 → ℝ, IsClassicalRep W a r := by
  have hrK : r ≤ K := by omega
  set a := AVRegularity.EntryWeakProofs.realClassicalLift K W with ha_def
  have ha : ContDiff ℝ (r : ℕ∞) a :=
    AVRegularity.EntryWeakProofs.realClassicalLift_contDiff K r h W
  have hp : AVenhance.IsZ2Periodic a :=
    AVRegularity.EntryWeakProofs.realClassicalLift_periodic K W
  set F := AVRegularity.EntryWeakProofs.classicalFiniteHk r a ha hp with hF
  set C : TorusHk r ℝ := F.toHk with hC
  -- `C` has the classical jet of `a` a.e. on the cell
  have hCae : ∀ b : JetIndex2 r, (C.val b : Vec 2 → ℝ) =ᵐ[volume.restrict AVenhance.unitCube]
      AVRegularity.EntryWeakProofs.classicalFiniteJet r a b := fun b =>
    torusJetToL2_ae F.jet F.hasPeriodicWeakJet.2.1 b
  have hCW : C = truncateTorusHk hrK W := by
    apply TorusHk.ext_value
    apply Lp.ext
    have hW := AVRegularity.EntryWeakProofs.realClassicalLift_value_ae K (by omega) W
    have h1 := hCae (valueIndex2 r)
    have hval : AVRegularity.EntryWeakProofs.classicalFiniteJet r a (valueIndex2 r) = a := by
      simp [AVRegularity.EntryWeakProofs.classicalFiniteJet, valueIndex2, valueIndex,
        AVRegularity.CoupledEnergy.Galerkin.smoothLiftWord,
        AVenhance.Infra.Classical.classicalWordDerivative]
    rw [hval] at h1
    exact h1.trans hW
  refine ⟨a, hrK, by exact_mod_cast ha, hp, fun m hm w => ?_⟩
  let b : JetIndex2 r := ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩
  have hjet : (fun x => torusJetOrder W m w x) =
      W.toFunction.jet ⟨⟨m, Nat.lt_succ_of_le (hm.trans hrK)⟩, w⟩ := by
    funext x
    simp [torusJetOrder, hm.trans hrK]
  have hWb : W.toFunction.jet ⟨⟨m, Nat.lt_succ_of_le (hm.trans hrK)⟩, w⟩
      =ᵐ[volume.restrict AVenhance.unitCube] (C.val b : Vec 2 → ℝ) := by
    have h1 := periodicJetRepresentative_ae W.val ⟨⟨m, Nat.lt_succ_of_le (hm.trans hrK)⟩, w⟩
    have h2 : C.val b = W.val ⟨⟨m, Nat.lt_succ_of_le (hm.trans hrK)⟩, w⟩ := by
      rw [hCW]; rfl
    rw [h2]
    exact h1
  have hcl : AVRegularity.EntryWeakProofs.classicalFiniteJet r a b = orderedDerivative w a := by
    rw [orderedDerivative_eq_classicalWordDerivative]
    rfl
  change torusJetOrder W m w =ᵐ[volume.restrict AVenhance.unitCube] orderedDerivative w a
  rw [show torusJetOrder W m w = fun x => torusJetOrder W m w x from rfl, hjet, ← hcl]
  exact hWb.trans (hCae b)

end AVRegularity.Providers
end
end

section
section
/-! Proof of `carrier_start_exists`.

Both conditions of `IsCarrierStart` are eventual consequences of powers of the parent wavelength
`ε_{m-1}` tending to zero: `a_kτ''_{k+1} ≤ 2^{-25}ε_k^{2δ}` (`admissible_time_scale_facts`), and
`τ''_{m+1}/τ_m = (τ''_{m+1}/τ'_m)L_m ≤ 9Cε_{m-1}^{qγ+(2q+4)δ}` (`tauRatio_bound`,
`ocL_power_bounds`). -/

@[expose] public section

open Filter Topology

namespace AVRegularity.Providers

/-- A positive power of the parent wavelength is eventually below any positive level. -/
theorem exists_parent_rpow_lt {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) {e c : ℝ}
    (he : 0 < e) (hc : 0 < c) : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ocEpsilon q Λ (m - 1) ^ e < c := by
  have h := (Real.continuousAt_rpow_const 0 e (Or.inr he.le)).tendsto.comp
    (AVRegularity.CycleReference.epsilon_parent_tendsto_zero (Λ := Λ) hq hΛ)
  rw [Real.zero_rpow he.ne'] at h
  exact eventually_atTop.1 (h (gt_mem_nhds hc))

/-- The history-separation ratio: `τ''_{m+1} ≤ 9Cε_{m-1}^{qγ+(2q+4)δ}τ_m` for `m ≥ 1`. -/
theorem tauPP_succ_le_tau {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℕ, 128 ≤ Λ → ∀ m : ℕ, 1 ≤ m →
      ocTauPP α q Λ (m + 1) ≤
        C * ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + (2 * q + 4) * ocDelta α q) *
          ocTau α q Λ m := by
  obtain ⟨C, hC, hrat⟩ := AVRegularity.EntryScales.tauRatio_bound hα₀ hα₁ hs₀ hs₁ hq
  refine ⟨9 * C, by positivity, fun Λ hΛ m hm => ?_⟩
  have hδ := (AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hE := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 hΛ
  have hfacts := AVRegularity.Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ hm
  have hL := hfacts.2.2.1
  have hr2 := hfacts.2.2.2.2.2.2.2.2
  have hΛ1 : 1 ≤ Λ := by omega
  have hτ : 0 < ocTau α q Λ m := AVRegularity.Construction.Stream.ocTau_pos hΛ1
  have hτP : 0 < ocTauP α q Λ m := AVRegularity.EntryScales.ocTauP_pos' hΛ1
  have h1 := hrat Λ hΛ m hm
  rw [div_le_iff₀ hτP] at h1
  -- `τ'_m = L_m τ_m`
  have hτP' : ocTauP α q Λ m = (ocL α q Λ m : ℝ) * ocTau α q Λ m := by
    rw [← hr2]; field_simp
  set a := q * ocGamma α q + (2 * q + 5) * ocDelta α q
  have hsplit : ocEpsilon q Λ (m - 1) ^ a * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) =
      ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + (2 * q + 4) * ocDelta α q) := by
    rw [← Real.rpow_add hE.1]; congr 1; ring
  have hpa : 0 ≤ ocEpsilon q Λ (m - 1) ^ a := Real.rpow_nonneg hE.1.le _
  calc ocTauPP α q Λ (m + 1) ≤ C * ocEpsilon q Λ (m - 1) ^ a * ocTauP α q Λ m := h1
    _ = C * ocEpsilon q Λ (m - 1) ^ a * (ocL α q Λ m : ℝ) * ocTau α q Λ m := by
        rw [hτP']; ring
    _ ≤ C * ocEpsilon q Λ (m - 1) ^ a * (9 * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)) *
          ocTau α q Λ m := by gcongr
    _ = 9 * C * ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + (2 * q + 4) * ocDelta α q) *
          ocTau α q Λ m := by rw [← hsplit]; ring

/-- **An admissible carrier start exists**. -/
theorem carrier_start_exists (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) :
    ∀ Λ : ℕ, 128 ≤ Λ → ∀ (b CH Υ : ℝ), 0 < b → ∃ j₀ : ℕ, IsCarrierStart α q Λ b CH Υ j₀ := by
  intro Λ hΛ b CH Υ hb
  have hfx := AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hγ := hfx.1
  have hδ := hfx.2.1
  have hq0 : 0 < q := by linarith [hq.1]
  obtain ⟨C, hC, hsep⟩ := tauPP_succ_le_tau hα₀ hα₁ hs₀ hs₁ hq
  set B : ℝ := b / (64 * (8 * Real.pi ^ 2)) with hB
  have hBpos : 0 < B := by positivity
  set K₁ : ℝ := 2 * (|Υ| * |CH| + 1)
  have hK₁ : 0 < K₁ := by positivity
  set K₂ : ℝ := 2 * (|CH| + 1)
  have hK₂ : 0 < K₂ := by positivity
  obtain ⟨N₁, hN₁⟩ := exists_parent_rpow_lt (Λ := Λ) hq.1 hΛ (e := 2 * ocDelta α q)
    (c := B / K₁) (by positivity) (by positivity)
  obtain ⟨N₂, hN₂⟩ := exists_parent_rpow_lt (Λ := Λ) hq.1 hΛ
    (e := q * ocGamma α q + (2 * q + 4) * ocDelta α q) (c := 1 / (24 * K₂ * C))
    (by positivity) (by positivity)
  refine ⟨max N₁ (max N₂ 1), fun k hk => ?_, fun m hm => ?_⟩
  · -- chain smallness at `m = k + 1`
    have hfacts := AVRegularity.Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ
      (m := k + 1) (by omega)
    have hAT := hfacts.2.2.2.2.1
    simp only [Nat.add_sub_cancel] at hAT
    have hsmall := hN₁ (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hsmall
    have hE := AVRegularity.Scales.epsilon_basic (m := k) hq.1 hΛ
    have hA0 : 0 ≤ ocA α q Λ k := Real.rpow_nonneg hE.1.le _
    have hT0 : 0 ≤ ocTauPP α q Λ (k + 1) :=
      (AVRegularity.Construction.Stream.ocTauPP_pos (by omega)).le
    have hX0 : 0 ≤ ocA α q Λ k * ocTauPP α q Λ (k + 1) := mul_nonneg hA0 hT0
    have h25 : (2 : ℝ) ^ (-25 : ℤ) ≤ 1 := by norm_num
    have hP0 : 0 ≤ ocEpsilon q Λ k ^ (2 * ocDelta α q) := Real.rpow_nonneg hE.1.le _
    have hX : ocA α q Λ k * ocTauPP α q Λ (k + 1) ≤ B / K₁ := by
      refine hAT.trans ?_
      nlinarith
    have hcoef : 2 * Υ * CH ≤ K₁ := by
      have h1 : Υ * CH ≤ |Υ| * |CH| := by rw [← abs_mul]; exact le_abs_self _
      simp only [K₁]; linarith
    calc 2 * Υ * CH * ocA α q Λ k * ocTauPP α q Λ (k + 1)
        = 2 * Υ * CH * (ocA α q Λ k * ocTauPP α q Λ (k + 1)) := by ring
      _ ≤ K₁ * (ocA α q Λ k * ocTauPP α q Λ (k + 1)) := mul_le_mul_of_nonneg_right hcoef hX0
      _ ≤ K₁ * (B / K₁) := mul_le_mul_of_nonneg_left hX hK₁.le
      _ = B := by field_simp
  · -- history separation
    have hm1 : 1 ≤ m := by omega
    have hτ : 0 < ocTau α q Λ m := AVRegularity.Construction.Stream.ocTau_pos (by omega)
    have h1 := hsep Λ hΛ m hm1
    have hsmall := hN₂ m (by omega)
    have hT0 : 0 ≤ ocTauPP α q Λ (m + 1) :=
      (AVRegularity.Construction.Stream.ocTauPP_pos (by omega)).le
    have hcoef : 2 * CH ≤ K₂ := by
      have := le_abs_self CH
      simp only [K₂]; linarith
    have hX : ocTauPP α q Λ (m + 1) < ocTau α q Λ m / (24 * K₂) := by
      refine h1.trans_lt ?_
      have : C * ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + (2 * q + 4) * ocDelta α q) <
          1 / (24 * K₂) := by
        calc C * ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + (2 * q + 4) * ocDelta α q)
            < C * (1 / (24 * K₂ * C)) := mul_lt_mul_of_pos_left hsmall hC
          _ = 1 / (24 * K₂) := by field_simp
      calc C * ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + (2 * q + 4) * ocDelta α q) *
            ocTau α q Λ m < 1 / (24 * K₂) * ocTau α q Λ m := mul_lt_mul_of_pos_right this hτ
        _ = ocTau α q Λ m / (24 * K₂) := by ring
    calc 2 * CH * ocTauPP α q Λ (m + 1) ≤ K₂ * ocTauPP α q Λ (m + 1) :=
          mul_le_mul_of_nonneg_right hcoef hT0
      _ < K₂ * (ocTau α q Λ m / (24 * K₂)) := mul_lt_mul_of_pos_left hX hK₂
      _ = ocTau α q Λ m / 24 := by field_simp

end AVRegularity.Providers
end
end

section
/-! Proof of `csNorm_trace_closure`.

Fix `t` in the window. Good times (those with a `C^s` representative) have full measure, so they
accumulate at `t`; a subsequence of their representatives converges pointwise to a continuous
periodic `Θ` with the same bound (`exists_csNormLe_limit`). Against every smooth periodic test,
the pairings of `θ` at the good times converge to the pairing of `θ(t)` (weak time continuity of
`IsWeakSolutionOn`) and, by dominated convergence, to the pairing of `Θ`; smooth periodic tests
separate `L²(unitCube)` (`ae_eq_zero_of_smooth_periodic_tests`), so `Θ = θ(t)` a.e. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity.Providers

open TraceClosure

private theorem unitCube_volume_lt_top : volume AVenhance.unitCube < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (t := Set.Icc (0 : Vec 2) 1) ?_) isCompact_Icc.measure_lt_top
  intro x hx
  exact ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2.le⟩

private instance traceClosureFiniteCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using unitCube_volume_lt_top⟩

/-- A continuous function is bounded on the unit cube. -/
private theorem exists_bound_unitCube {ψ : Vec 2 → ℝ} (hψ : Continuous ψ) :
    ∃ C : ℝ, ∀ x ∈ AVenhance.unitCube, |ψ x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Vec 2)) (b := 1)).exists_bound_of_continuousOn
    hψ.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  have hxI : x ∈ Set.Icc (0 : Vec 2) 1 :=
    ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2.le⟩
  simpa [Real.norm_eq_abs] using hC x hxI

/-- Points of a full-measure subset of a nondegenerate window accumulate at every point of it. -/
private theorem exists_good_near {t₁ t₂ t : ℝ} (ht₁₂ : t₁ < t₂) (ht : t ∈ Set.Icc t₁ t₂)
    {P : ℝ → Prop} (hP : ∀ᵐ τ ∂(volume.restrict (Set.Icc t₁ t₂)), P τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ ∈ Set.Icc t₁ t₂, |τ - t| < ε ∧ P τ := by
  have hpos : (volume.restrict (Set.Icc t₁ t₂)) (Set.Ioo (t - ε) (t + ε)) ≠ 0 := by
    rw [Measure.restrict_apply measurableSet_Ioo]
    have hsub : Set.Ioo (max (t - ε) t₁) (min (t + ε) t₂) ⊆
        Set.Ioo (t - ε) (t + ε) ∩ Set.Icc t₁ t₂ := fun y hy =>
      ⟨⟨lt_of_le_of_lt (le_max_left _ _) hy.1, lt_of_lt_of_le hy.2 (min_le_left _ _)⟩,
        ⟨(le_max_right _ _).trans hy.1.le, hy.2.le.trans (min_le_right _ _)⟩⟩
    have hlt : max (t - ε) t₁ < min (t + ε) t₂ := by
      rcases ht with ⟨h1, h2⟩
      refine max_lt (lt_min (by linarith) (by linarith)) (lt_min (by linarith) ht₁₂)
    refine fun h0 => ?_
    have := measure_mono_null hsub h0
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
    linarith
  have hall : ∀ᵐ τ ∂(volume.restrict (Set.Icc t₁ t₂)), τ ∈ Set.Icc t₁ t₂ ∧ P τ :=
    (ae_restrict_mem measurableSet_Icc).and hP
  obtain ⟨τ, hτ, hτI, hτP⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hall)
  exact ⟨τ, hτI, abs_sub_lt_iff.2 ⟨by linarith [hτ.2], by linarith [hτ.1]⟩, hτP⟩

/-- **Every-time closure of a uniform `C^s` bound**. -/
theorem csNorm_trace_closure (s : ℝ) (hs₀ : 0 < s) (_hs₁ : s < 1)
    (bv : ℝ → Vec 2 → Vec 2) (κ a b : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn bv κ a b f θ) (t₁ t₂ B : ℝ) (ht₁ : a ≤ t₁) (ht₁₂ : t₁ < t₂)
    (ht₂ : t₂ ≤ b)
    (hae : ∀ᵐ t ∂(volume.restrict (Set.Icc t₁ t₂)), ∃ Θt : Vec 2 → ℝ,
      IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧ CsNormLe s Θt B) :
    ∀ t ∈ Set.Icc t₁ t₂, ∃ Θt : Vec 2 → ℝ,
      IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧ CsNormLe s Θt B := by
  intro t ht
  obtain ⟨Dθ, hslice, -, -, -, -, -, hcont, -⟩ := hθ
  have hgood : ∀ n : ℕ, ∃ τ ∈ Set.Icc t₁ t₂, |τ - t| < 1 / ((n : ℝ) + 1) ∧
      ∃ Θt : Vec 2 → ℝ, IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ τ ∧
        CsNormLe s Θt B := fun n =>
    exists_good_near ht₁₂ ht hae (by positivity)
  choose τ hτI hτt Θ hΘper hΘae hΘcs using hgood
  obtain ⟨φ, Θl, hφ, hpt, hper, hcs, hc⟩ := exists_csNormLe_limit hs₀ Θ hΘper hΘcs
  refine ⟨Θl, hper, ?_, hcs⟩
  -- the good times converge to `t`
  have hτlim : Tendsto τ atTop (𝓝 t) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have hmono : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
    linarith [hτt n]
  have hτφ : Tendsto (fun k => τ (φ k)) atTop (𝓝 t) := hτlim.comp hφ.tendsto_atTop
  have hIab : Set.Icc t₁ t₂ ⊆ Set.Icc a b := Set.Icc_subset_Icc ht₁ ht₂
  have htab : t ∈ Set.Icc a b := hIab ht
  have hθt : MemL2On unitCube (θ t) := (hslice t htab).2
  have hB : 0 ≤ B := AVRegularity.Applications.csNormLe_K_nonneg hcs
  have hΘlb : ∀ x, |Θl x| ≤ B := abs_le_of_csNormLe hcs
  have hΘlm : MemL2On unitCube Θl := by
    refine memLp_of_bounded (a := -B) (b := B) (Eventually.of_forall fun x => ?_)
      hc.aestronglyMeasurable 2
    exact abs_le.1 (hΘlb x)
  have hcube : MeasurableSet unitCube := by
    simpa [AVenhance.unitCube, Set.pi] using
      (MeasurableSet.univ_pi' (fun _ : Fin 2 =>
        (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1))))
  -- the pairing identity against smooth periodic tests
  have hpair : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ∫ x in unitCube, (θ t x - Θl x) * ψ x = 0 := by
    intro ψ hψ hψp
    obtain ⟨C, hC⟩ := exists_bound_unitCube hψ.continuous
    have h1 : Tendsto (fun k => ∫ x in unitCube, θ (τ (φ k)) x * ψ x) atTop
        (𝓝 (∫ x in unitCube, θ t x * ψ x)) :=
      ((hcont ψ hψ hψp) t htab).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hτφ, Eventually.of_forall fun k => hIab (hτI _)⟩)
    have h3 : (fun k => ∫ x in unitCube, θ (τ (φ k)) x * ψ x) =
        fun k => ∫ x in unitCube, Θ (φ k) x * ψ x := by
      funext k
      refine integral_congr_ae ?_
      filter_upwards [hΘae (φ k)] with x hx
      rw [hx]
    rw [h3] at h1
    have h2 : Tendsto (fun k => ∫ x in unitCube, Θ (φ k) x * ψ x) atTop
        (𝓝 (∫ x in unitCube, Θl x * ψ x)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => B * C) (fun k => ?_)
        (integrable_const (B * C)) (fun k => ?_) (Eventually.of_forall fun x => ?_)
      · exact ((AVRegularity.Applications.continuous_of_csNormLe hs₀ (hΘcs (φ k))).mul
          hψ.continuous).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem hcube] with x hx
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_le_of_csNormLe (hΘcs (φ k)) x) (hC x hx) (abs_nonneg _) hB
      · exact (hpt x).mul tendsto_const_nhds
    have heq := tendsto_nhds_unique h1 h2
    have hiθ : Integrable (fun x => θ t x * ψ x) (volume.restrict unitCube) :=
      Integrable.mul_bdd (c := C) (hθt.integrable one_le_two) hψ.continuous.aestronglyMeasurable
        (by
          filter_upwards [ae_restrict_mem hcube] with x hx
          rw [Real.norm_eq_abs]; exact hC x hx)
    have hiΘ : Integrable (fun x => Θl x * ψ x) (volume.restrict unitCube) :=
      Integrable.mul_bdd (c := C) (hΘlm.integrable one_le_two) hψ.continuous.aestronglyMeasurable
        (by
          filter_upwards [ae_restrict_mem hcube] with x hx
          rw [Real.norm_eq_abs]; exact hC x hx)
    simp only [sub_mul]
    rw [integral_sub hiθ hiΘ, heq, sub_self]
  have hzero := ae_eq_zero_of_smooth_periodic_tests (hθt.sub hΘlm) hpair
  filter_upwards [hzero] with x hx
  have : θ t x - Θl x = 0 := hx
  linarith

end AVRegularity.Providers
end
end
end
