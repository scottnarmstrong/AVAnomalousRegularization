-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovarianceFluxRegLiftFlux
import AVRegularity.CycleComparison.Reconstruction.PulseChart
import AVRegularity.Construction.StrainPhysical.Context
public import AVRegularity.Proofs.QuietAtlas.PiolaGeom
import AVRegularity.Proofs.QuietAtlas.FirstSourceRenewal
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.Flux
public import AVRegularity.Construction.Preservation.Residual.WeakFluxTesting
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.SingleModeFlux
import AVenhance.Infra.Flow.CurveUniqueness
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Int.Star

section
section
/-! **The path mean of high degree vanishes** (the degree count of the cascade flux order bound
`cascadeFluxOrderBound`).

For a localized lift sequence of truncation order `N` (`IsLiftSequenceOn`) whose source edges of
order above `E'` vanish, the slow flux `liftFluxX` of degree `n > N + E'` vanishes at the admissible
slow offsets, at the times of the lift window:

* terms 1-3 of `liftFluxX` contain `C_{n-1}`, `C_{n-2}`, which vanish for `n - 2 > N`;
* the term `j` of the source sum contains `C_{n-j}` (zero for `n - j > N`), and otherwise
  `j - 1 ≥ E'`: the `ε^{j-1}` coefficient of `sourceFlux` only contains words of length `≥ j - 1`,
  that is edges of order `≥ j > E'` (`fluxG_grade_eq_zero`, from `gSupp_wordG`).

No regularity of the edges is used (their coefficients are scalar factors). The lift coefficients
are cut off around the offset (`exists_ball_cutoff`, `cutoffCoeff`) to apply the array form
`sourceFlux_apply`; the cut-off does not change the flux at the offset (`LocEq.sourceFlux`).

* `fluxG_grade_eq_zero`, `iteratedDeriv_sourceFlux_eq_zero_of_degree`,
  `liftFluxX_single_eq_zero_of_degree`, `pathMeanFlux_eq_zero_of_degree`.

For `N = 0` only `C_0` occurs; for `Dm < 2` there is no edge and no source term, and for
`hh = 0` there is no source term. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev MeasureTheory
open AVRegularity.Providers.GenSem

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.OrderBound

variable {ι : Type} [Fintype ι] {Dm : ℕ}

/-- The grade `p` of the graded flux array vanishes when the edges of order above `p` vanish: a
word of length `d - 1` has no grade `≥ d`. -/
theorem fluxG_grade_eq_zero (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (s t : ℝ) (k : Fin 2)
    {K : ℕ} {A : ι → CArr} (hs : ∀ v, ArrSupp K (A v)) (v : ι) {p : ℕ}
    (hedge : ∀ u (d : Finset.Icc 2 Dm), p < d.1 → ∀ γ ∈ edge v u d, ∀ α X z,
      γ.coeff α t X z k = 0) :
    fluxG edge s t k A v p = 0 := by
  let S : AddSubgroup (ℕ → CArr) :=
    { carrier := {P | P p = 0}
      zero_mem' := rfl
      add_mem' := fun {a b} ha hb => by
        show (a + b) p = 0
        rw [Pi.add_apply, ha, hb, add_zero]
      neg_mem' := fun {a} ha => by
        show (-a) p = 0
        rw [Pi.neg_apply, ha, neg_zero] }
  have hmem : fluxG edge s t k A v ∈ S := by
    unfold fluxG
    refine S.sum_mem fun u _ => S.sum_mem fun d _ => S.list_sum_mem fun P hP => ?_
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hP
    refine S.sum_mem fun α _ => ?_
    show wordG s (fun X z => γ.coeff α t X z k * γ.map 1) (d.1 - 1) α (A u) p = 0
    by_cases hd : p < d.1
    · have hg : (fun X z => γ.coeff α t X z k * γ.map 1) = fun _ _ => (0 : ℝ) := by
        funext X z
        rw [hedge u d hd γ hγ α X z, zero_mul]
      rw [hg]
      funext m β X z
      simp [wordG, mulG, mulArr]
    · have hd2 := (Finset.mem_Icc.mp d.2).1
      exact (gSupp_wordG (hs u) s _ α).2 p (by omega)
  exact hmem

variable [DecidableEq ι]

/-- One term of the source sum of `liftFluxX`, of degree `n > N + E'`. -/
theorem iteratedDeriv_sourceFlux_eq_zero_of_degree (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) {Ω : Set (Vec 2)} (hΩ : IsOpen Ω)
    {sX sZ N H E' : ℕ} {t₀ t₁ : ℝ} (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N H Cc)
    (hsX : Dm ≤ sX) (hsZ : Dm ≤ sZ) {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁)
    (hedge : ∀ v u (d : Finset.Icc 2 Dm), E' < d.1 → ∀ γ ∈ Q.edge v u d, ∀ α X z k,
      γ.coeff α s X z k = 0)
    {hh' n j : ℕ} (hhH : hh' ≤ H) (hj1 : 1 ≤ j) (hjD : j ≤ Dm) (hn : N + E' < n)
    (w : ι) {a₀ : Vec 2 → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) {X : Vec 2} (hX : X ∈ Ω)
    (z : Vec 2) (κ : Fin 2) :
    iteratedDeriv (j - 1) (fun ε : ℝ => sourceFlux Q.edge Q.η ε s
      (liftApply (n - j) (Cc hh' (n - j)) (fun _ Y => (Pi.single w (a₀ Y) : ι → ℝ)) s) κ X z)
      0 = 0 := by
  by_cases hnj : N < n - j
  · -- the lift coefficient `C_{n-j}` vanishes
    have hL : liftApply (n - j) (Cc hh' (n - j))
        (fun _ Y => (Pi.single w (a₀ Y) : ι → ℝ)) s = fun _ _ => 0 := by
      funext Y z' v
      simp [liftApply, hC.2.2.1 hh' hhH (n - j) hnj]
    rw [hL]
    funext v
    refine CycleComparison.Reconstruction.iteratedDeriv_apply_eq_zero (fun ε => ?_) (j - 1) 0
    show sourceFlux Q.edge Q.η ε s (fun _ _ => (0 : ι → ℝ)) κ X z v = 0
    unfold sourceFlux
    refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun d _ =>
      List.sum_eq_zero fun x hx => ?_
    obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hx
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [CycleComparison.Reconstruction.dEpsWord_apply_eq_zero (fun _ _ => rfl) α X z, map_zero,
      smul_zero]
  · -- `E' ≤ j - 1`: the `ε^{j-1}` coefficient needs edges of order `≥ j`
    have hjE : E' ≤ j - 1 := by omega
    have htop : ∀ r : ℕ, ((r : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun r => by
      exact_mod_cast le_top
    obtain ⟨r, hr, χ, hχ, hsupp, h1⟩ := exists_ball_cutoff hΩ hX
    have hloc : Uniqueness.LocEq (Metric.ball X r)
        (liftApply (n - j) (Cc hh' (n - j)) (fun _ Y => (Pi.single w (a₀ Y) : ι → ℝ)) s)
        (liftApply (n - j) (cutoffCoeff χ Cc hh' (n - j))
          (fun _ Y => (Pi.single w (a₀ Y) : ι → ℝ)) s) :=
      Uniqueness.liftApply_locEq Metric.isOpen_ball
        (fun m _ α Y hY => (cutoffCoeff_eq h1 hh' (n - j) m α s hY).symm) (fun _ _ => rfl)
    have hΦ' : liftApply (n - j) (cutoffCoeff χ Cc hh' (n - j))
        (fun _ Y => (Pi.single w (a₀ Y) : ι → ℝ)) s =
        fun Y z' v => applyArr (n - j)
          (entryArr (cutoffCoeff χ Cc hh' (n - j)) (n - j) w s v) a₀ Y z' := by
      funext Y z' v
      exact liftApply_single (n - j) (cutoffCoeff χ Cc hh' (n - j)) w
        (ha.of_le (htop _)) s Y z' v
    have hAs : ∀ v, ArrSmooth Dm (entryArr (cutoffCoeff χ Cc hh' (n - j)) (n - j) w s v) :=
      fun v => arrSmooth_entryArr _ _ _ _ _ fun m α =>
        contDiff_cutoffCoeff hΩ hχ hsupp (contDiffOn_coeff_of_box hΩ
          (hC.2.2.2.2.2.1 hh' hhH (n - j) m α v w s hs).1 hsX hsZ)
    have hAsupp : ∀ v, ArrSupp (n - j)
        (entryArr (cutoffCoeff χ Cc hh' (n - j)) (n - j) w s v) :=
      fun v => arrSupp_entryArr _ _ _ _ _
    have hpoly : CovFluxReg.PolyAt (fun ε : ℝ => sourceFlux Q.edge Q.η ε s
        (liftApply (n - j) (Cc hh' (n - j)) (fun _ Y => (Pi.single w (a₀ Y) : ι → ℝ)) s) κ X z)
        Dm (fun p => fun v => applyArr (n - j + Dm) (fluxG Q.edge (Real.sqrt Q.η) s κ
          (fun v => entryArr (cutoffCoeff χ Cc hh' (n - j)) (n - j) w s v) v p) a₀ X z) := by
      intro ε
      beta_reduce
      funext v
      rw [(hloc.sourceFlux Metric.isOpen_ball Q.edge Q.η ε s κ) X (Metric.mem_ball_self hr) z,
        hΦ', sourceFlux_apply Q.edge Q.η ε s κ (ha.of_le (htop _)) hAs hAsupp
          X z v, evalApplyHom_apply]
      simp only [evalG, applyArr_sum, applyArr_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
    rw [hpoly.iteratedDeriv_zero (by omega : j - 1 < Dm)]
    have hz : (fun v => applyArr (n - j + Dm) (fluxG Q.edge (Real.sqrt Q.η) s κ
        (fun v => entryArr (cutoffCoeff χ Cc hh' (n - j)) (n - j) w s v) v (j - 1)) a₀ X z) =
        (0 : ι → ℝ) := by
      funext v
      rw [fluxG_grade_eq_zero Q.edge (Real.sqrt Q.η) s κ hAsupp v
        (fun u d hd γ hγ α Y z' => hedge v u d (by omega) γ hγ α Y z' κ), applyArr_zero]
      rfl
    rw [hz, smul_zero]

/-- **The slow flux of degree `n > N + E'` vanishes** at the admissible offsets, on a test field
in one component. -/
theorem liftFluxX_single_eq_zero_of_degree (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) {Ω : Set (Vec 2)} (hΩ : IsOpen Ω)
    {sX sZ N H E' : ℕ} {t₀ t₁ : ℝ} (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N H Cc)
    (hsX : Dm ≤ sX) (hsZ : Dm ≤ sZ) (hE' : 2 ≤ E') {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁)
    (hedge : ∀ v u (d : Finset.Icc 2 Dm), E' < d.1 → ∀ γ ∈ Q.edge v u d, ∀ α X z k,
      γ.coeff α s X z k = 0)
    {hh n : ℕ} (hhH : hh ≤ H) (hn : N + E' < n)
    (w : ι) {a₀ : Vec 2 → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) {X : Vec 2} (hX : X ∈ Ω)
    (z : Vec 2) (κ : Fin 2) :
    liftFluxX Q Cc (fun _ Y => (Pi.single w (a₀ Y) : ι → ℝ)) hh n s X z κ = 0 := by
  have h1 : liftApply (n - 1) (Cc hh (n - 1))
      (fun _ Y => (Pi.single w (a₀ Y) : ι → ℝ)) s = fun _ _ => 0 := by
    funext Y z' v
    simp [liftApply, hC.2.2.1 hh hhH (n - 1) (by omega)]
  have h2 : liftApply (n - 2) (Cc hh (n - 2))
      (fun _ Y => (Pi.single w (a₀ Y) : ι → ℝ)) s = fun _ _ => 0 := by
    funext Y z' v
    simp [liftApply, hC.2.2.1 hh hhH (n - 2) (by omega)]
  have h4 : (if hh = 0 then (0 : ι → ℝ) else ∑ j ∈ Finset.Icc 1 (min Dm n),
      (Real.sqrt Q.η * ((j - 1).factorial : ℝ)⁻¹) •
        iteratedDeriv (j - 1) (fun ε : ℝ => sourceFlux Q.edge Q.η ε s
          (liftApply (n - j) (Cc (hh - 1) (n - j))
            (fun _ Y => (Pi.single w (a₀ Y) : ι → ℝ)) s) κ X z) 0) = 0 := by
    split_ifs with h0
    · rfl
    · refine Finset.sum_eq_zero fun j hj => ?_
      have hj' := Finset.mem_Icc.mp hj
      rw [iteratedDeriv_sourceFlux_eq_zero_of_degree Q Cc hΩ hC hsX hsZ hs hedge
        (by omega : hh - 1 ≤ H) hj'.1 (hj'.2.trans (min_le_left _ _)) hn w ha hX z κ, smul_zero]
  unfold liftFluxX
  rw [h1, h2, h4]
  simp [fastPartial, slowPartial]

/-- **The path mean of degree `n > N + E'` vanishes** at the labels of the admissible offsets, on
smooth test fields. -/
theorem pathMeanFlux_eq_zero_of_degree (D : OCData) (m : ℕ) (ρ : ℝ) {h : ℕ}
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) {Ω : Set (Vec 2)} (hΩ : IsOpen Ω)
    {sX sZ N E' : ℕ} {t₀ t₁ : ℝ} (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N h Cc)
    (hsX : Dm ≤ sX) (hsZ : Dm ≤ sZ) (hE' : 2 ≤ E') {t : ℝ}
    (hs : (D.cellScaleSq m)⁻¹ * t ∈ Set.Icc t₀ t₁)
    (hedge : ∀ v u (d : Finset.Icc 2 Dm), E' < d.1 → ∀ γ ∈ Q.edge v u d, ∀ α X z k,
      γ.coeff α ((D.cellScaleSq m)⁻¹ * t) X z k = 0)
    {n : ℕ} (hn : N + E' < n) {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {y : Vec 2}
    (hy : ρ⁻¹ • y ∈ Ω) :
    pathMeanFlux D m ρ Q Cc n t f y = 0 := by
  funext κ
  unfold pathMeanFlux
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun X : Vec 2 => f (ρ • X)) :=
    hf.comp (contDiff_const_smul ρ)
  have hz : (fun z => liftFluxX Q Cc
      (fun _ X => (Pi.single (0 : Fin (h + 1)) (f (ρ • X)) : Fin (h + 1) → ℝ)) h n
      ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z κ) = fun _ => 0 :=
    funext fun z => liftFluxX_single_eq_zero_of_degree Q Cc hΩ hC hsX hsZ hE' hs hedge le_rfl
      hn 0 ha hy z κ
  rw [hz]
  simp [fieldCellMean]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.OrderBound
end
end

section
/-! Transfer collapse, the geometric core: **the flow of level `m` between two
times at which only the pulse `p` acts**.

`OCData.Φ` is an arbitrary admissible stream sequence. Under `IsOCStreamSeq`, at a time `v` with
`|v - p τ_m| < (4/3) τ_m` the only pulse of level `m` that can act is `p` (the profile vanishes
outside `(-2/3, 2/3)`, and the windows of `p ± 2` cover the two quiet margins), so the velocity
increment of the level is the transported shear of `p` (`singlePulseAt_of_near`, from
`streamVel_increment_of_base`, which is `StrainPhysical.streamVel_increment` for `1 ≤ Λ` without
its hypotheses `0 < α`, `1 < q`). Between two such times the material equation in the labels
of the anchor `s_p` is the shear `ẇ = p_p(u) 𝐮_p(w)`, which preserves `𝐮_p(w)`, hence
`X_m(u, x, r) = X_{m-1}(u, w + (∫_r^u p_p) 𝐮_p(w), s_p)`, `w = X_{m-1}(s_p, x, r)`
(`flowOf_single_pulse`, by uniqueness of integral curves on the interval). This is the offset
flow of a child of the native chain of `p` (`OCData.childGeom`), at every time, quiet or not. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- At the time `v` the velocity increment of the level `m` is the transported shear of the
pulse `p` alone. -/
def SinglePulseAt (D : OCData) (m : ℕ) (p : ℤ) (v : ℝ) : Prop :=
  ∀ x : Vec 2, streamVel (D.Φ m) v x = streamVel (D.Φ (m - 1)) v x +
    ocPulse D.α D.q D.Λ D.ζ m p v •
      fderiv ℝ (fun z => D.flowOf (m - 1) v z (D.slotAnchor m p))
        (D.flowOf (m - 1) (D.slotAnchor m p) x v)
        (ocShearVel D.α D.q D.Λ m p (D.flowOf (m - 1) (D.slotAnchor m p) x v))

/-- A pulse vanishes at the times farther than `(2/3) τ` from its centre. -/
theorem ocPulse_eq_zero_of_far {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) {m : ℕ}
    (hτ : 0 < ocTau α q Λ m) {k : ℤ} {v : ℝ}
    (h : 2 / 3 * ocTau α q Λ m ≤ |v - (k : ℝ) * ocTau α q Λ m|) : ocPulse α q Λ ζ m k v = 0 := by
  unfold ocPulse
  rw [StrainPhysical.zeta_eq_zero_of_far hζ (by rw [abs_div, abs_of_pos hτ, le_div_iff₀ hτ]; exact h),
    mul_zero]

section Increment
open StrainPhysical CycleReference

/-- The increment identity on the window of the pulse `pc` (with `Ψ x = X(s_pc, x, t)`), for
`1 ≤ Λ`: `StrainPhysical.streamVel_increment` without its hypotheses `0 < α`, `1 < q`, which serve
only its case `Λ = 0` (the same proof). -/
theorem streamVel_increment_of_base {α q : ℝ} {Λ : ℕ} (hΛ1 : 1 ≤ Λ) {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ} {i : ℕ}
    {h : IsAdmissibleStream (Φ (i - 1))}
    (hnext : Φ i = ocNextStream α q Λ ζ i (Φ (i - 1)) h) {pc : ℤ} (hpc : Odd pc) {t : ℝ}
    (ht : t ∈ ocPulseWindow α q Λ i pc) (x : Vec 2) :
    streamVel (Φ i) t x = streamVel (Φ (i - 1)) t x +
      ocPulse α q Λ ζ i pc t •
        fderiv ℝ (fun z => AVRegularity.streamFlow (Φ (i - 1)) h t z
            ((ocLabel α q Λ i pc : ℝ) * ocTauPP α q Λ i))
          (AVRegularity.streamFlow (Φ (i - 1)) h ((ocLabel α q Λ i pc : ℝ) * ocTauPP α q Λ i) x t)
          (ocShearVel α q Λ i pc
            (AVRegularity.streamFlow (Φ (i - 1)) h ((ocLabel α q Λ i pc : ℝ) * ocTauPP α q Λ i)
              x t)) := by
  set s := (ocLabel α q Λ i pc : ℝ) * ocTauPP α q Λ i with hs
  set Ψ : Vec 2 → Vec 2 := fun z => AVRegularity.streamFlow (Φ (i - 1)) h s z t with hΨ
  -- the function identity
  have hfun : Φ i t = fun x' => Φ (i - 1) t x' +
      ocPulse α q Λ ζ i pc t * ocShear α q Λ i pc (Ψ x') := by
    funext x'
    rw [hnext]
    unfold ocNextStream
    congr 1
    · have hτ : 0 < ocTau α q Λ i := AVRegularity.Construction.Stream.ocTau_pos hΛ1
      rw [tsum_eq_single pc]
      · simp only [ocPulse, hΨ, hs]
        rfl
      · intro k hk
        by_cases hko : Odd k
        · have hdiff : 2 ≤ |(k : ℝ) - (pc : ℝ)| := by
            obtain ⟨a, ha⟩ := hko
            obtain ⟨b, hb⟩ := hpc
            have hab : a ≠ b := by intro hh; apply hk; rw [ha, hb, hh]
            have : (2 : ℤ) ≤ |k - pc| := by
              rw [ha, hb]
              have : 2 * a + 1 - (2 * b + 1) = 2 * (a - b) := by ring
              rw [this, abs_mul]
              have : 1 ≤ |a - b| := Int.one_le_abs (sub_ne_zero.2 hab)
              simp only [abs_two]
              omega
            have h2 : ((2 : ℤ) : ℝ) ≤ ((|k - pc| : ℤ) : ℝ) := by exact_mod_cast this
            simpa [Int.cast_abs] using h2
          have hz : ζ ((t - (k : ℝ) * ocTau α q Λ i) / ocTau α q Λ i) = 0 := by
            apply zeta_eq_zero_of_far hζ
            obtain ⟨hl, hu⟩ := ht
            have hl' : ((pc : ℝ) - 61 / 48) ≤ t / ocTau α q Λ i := by
              rw [le_div_iff₀ hτ]; exact hl
            have hu' : t / ocTau α q Λ i ≤ ((pc : ℝ) + 61 / 48) := by
              rw [div_le_iff₀ hτ]; exact hu
            have e : (t - (k : ℝ) * ocTau α q Λ i) / ocTau α q Λ i =
                t / ocTau α q Λ i - k := by field_simp
            rw [e]
            rcases le_abs'.1 hdiff with h1 | h1
            · rw [abs_of_nonneg (by linarith)]; linarith
            · rw [abs_of_nonpos (by linarith)]; linarith
          simp [hz]
        · have h1 : k % 4 ≠ 1 := by
            intro hh; apply hko; exact ⟨k / 2, by omega⟩
          have h3 : k % 4 ≠ 3 := by
            intro hh; apply hko; exact ⟨k / 2, by omega⟩
          have : ocShear α q Λ i k = fun _ => 0 := by
            funext y
            rw [ocShear_sine_formula]
            simp [h1, h3]
          simp [this]
  have hψd : Differentiable ℝ (ocShear α q Λ i pc) :=
    (ocShear_contDiff α q Λ i pc).differentiable (by simp)
  have hΨd : Differentiable ℝ Ψ := differentiable_flow h s t
  have hφd := differentiable_slice h t
  have hgrad : spaceGrad (Φ i t) x = spaceGrad (Φ (i - 1) t) x +
      ocPulse α q Λ ζ i pc t • spaceGrad (ocShear α q Λ i pc ∘ Ψ) x := by
    rw [hfun]
    ext k
    simp only [spaceGrad, Pi.add_apply, Pi.smul_apply]
    have hd := (hφd x).hasFDerivAt.add (((hψd.comp hΨd) x).hasFDerivAt.const_mul
      (ocPulse α q Λ ζ i pc t))
    have hd' : fderiv ℝ (fun x' => Φ (i - 1) t x' + ocPulse α q Λ ζ i pc t *
        ocShear α q Λ i pc (Ψ x')) x = _ := hd.fderiv
    rw [hd']
    simp
  change sigmaMat.mulVec (spaceGrad (Φ i t) x) = _
  rw [hgrad, Matrix.mulVec_add, Matrix.mulVec_smul]
  congr 1
  congr 1
  exact stream_transport h t s x (hψd _)

end Increment

/-- **Only the pulse `p` acts within `(4/3) τ_m` of its centre.** -/
theorem singlePulseAt_of_near {D : OCData} (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) {m : ℕ} (hm : 1 ≤ m)
    {p : ℤ} (hp : Odd p) {v : ℝ}
    (hv : |v - (p : ℝ) * ocTau D.α D.q D.Λ m| < 4 / 3 * ocTau D.α D.q D.Λ m) :
    SinglePulseAt D m p v := by
  obtain ⟨h, hnext⟩ := hseq.2 m hm
  have hτ : 0 < ocTau D.α D.q D.Λ m := Construction.Stream.ocTau_pos hΛ
  obtain ⟨hv1, hv2⟩ := abs_lt.mp hv
  by_cases hw : v ∈ ocPulseWindow D.α D.q D.Λ m p
  · exact fun x => streamVel_increment_of_base hΛ hζ hnext hp hw x
  · -- a quiet margin: the neighbour `p'` has `v` in its window, and both pulses vanish
    have key : ∀ p' : ℤ, Odd p' → v ∈ ocPulseWindow D.α D.q D.Λ m p' →
        2 / 3 * ocTau D.α D.q D.Λ m ≤ |v - (p' : ℝ) * ocTau D.α D.q D.Λ m| →
        2 / 3 * ocTau D.α D.q D.Λ m ≤ |v - (p : ℝ) * ocTau D.α D.q D.Λ m| →
        SinglePulseAt D m p v := by
      intro p' hp' hw' hfar' hfar x
      have h1 := streamVel_increment_of_base hΛ hζ hnext hp' hw' x
      rw [ocPulse_eq_zero_of_far hζ hτ hfar', zero_smul, add_zero] at h1
      rw [h1, ocPulse_eq_zero_of_far hζ hτ hfar, zero_smul, add_zero]
    have hw' : ¬ ((((p : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ m ≤ v) ∧
        v ≤ ((p : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) := hw
    rcases not_and_or.mp hw' with hlow | hhigh
    · -- `v` below the window of `p`: the neighbour is `p - 2`
      have hlow' := not_le.mp hlow
      have hodd : Odd (p - 2) := by
        obtain ⟨a, ha⟩ := hp
        exact ⟨a - 1, by omega⟩
      have hcast : ((p - 2 : ℤ) : ℝ) = (p : ℝ) - 2 := by push_cast; ring
      refine key (p - 2) hodd ⟨?_, ?_⟩ ?_ ?_
      · rw [hcast]; nlinarith
      · rw [hcast]; nlinarith
      · rw [hcast, le_abs]; left; nlinarith
      · rw [le_abs]; right; nlinarith
    · -- `v` above the window of `p`: the neighbour is `p + 2`
      have hhigh' := not_le.mp hhigh
      have hodd : Odd (p + 2) := by
        obtain ⟨a, ha⟩ := hp
        exact ⟨a + 1, by omega⟩
      have hcast : ((p + 2 : ℤ) : ℝ) = (p : ℝ) + 2 := by push_cast; ring
      refine key (p + 2) hodd ⟨?_, ?_⟩ ?_ ?_
      · rw [hcast]; nlinarith
      · rw [hcast]; nlinarith
      · rw [hcast, le_abs]; right; nlinarith
      · rw [le_abs]; left; nlinarith

/-- The inverse law of a flow at a fixed pair of times. -/
theorem flowOf_inv (D : OCData) (k : ℕ) (a b' : ℝ) (y : Vec 2) :
    D.flowOf k a (D.flowOf k b' y a) b' = y := by
  rw [Providers.QuietAtlas.flowOf_group, Providers.QuietAtlas.flowOf_self]

/-- **The flow of level `m` between two times of a single pulse `p`** is the flow of level
`m - 1` after the shear displacement in the labels of the anchor `s_p`. -/
theorem flowOf_single_pulse {D : OCData} (hζ : IsFastProfile D.ζ) {m : ℕ} {p : ℤ} {r u : ℝ}
    (hsp : ∀ v ∈ Set.uIcc r u, SinglePulseAt D m p v) (x : Vec 2) :
    D.flowOf m u x r = D.flowOf (m - 1) u
      (D.flowOf (m - 1) (D.slotAnchor m p) x r +
        (∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ m p v) •
          ocShearVel D.α D.q D.Λ m p (D.flowOf (m - 1) (D.slotAnchor m p) x r))
      (D.slotAnchor m p) := by
  set s := D.slotAnchor m p with hs
  set w := D.flowOf (m - 1) s x r with hw
  set U := ocShearVel D.α D.q D.Λ m p w with hU
  have hc : Continuous (ocPulse D.α D.q D.Λ D.ζ m p) := CycleReference.ocPulse_continuous hζ p
  -- the curve of the right-hand side
  let W : ℝ → Vec 2 := fun u' => w + (∫ v in r..u', ocPulse D.α D.q D.Λ D.ζ m p v) • U
  let F : ℝ × Vec 2 → Vec 2 := fun q => D.flowOf (m - 1) q.1 q.2 s
  let γ : ℝ → Vec 2 := fun u' => F (u', W u')
  let η : ℝ → Vec 2 := fun u' => D.flowOf m u' x r
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F :=
    (CycleReference.streamFlow_joint_smooth (D.hΦ (m - 1))).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
  have hFd : Differentiable ℝ F := hFs.differentiable (by simp)
  have hflow := AVenhance.flow_isFlow (streamVel (D.Φ (m - 1))) (D.hΦ (m - 1)).vel_continuous
    (D.hΦ (m - 1)).vel_lipschitz
  have hflowm := AVenhance.flow_isFlow (streamVel (D.Φ m)) (D.hΦ m).vel_continuous
    (D.hΦ m).vel_lipschitz
  have hW : ∀ u', HasDerivAt W (ocPulse D.α D.q D.Λ D.ζ m p u' • U) u' := fun u' =>
    ((intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).smul_const U).const_add w
  -- the partial derivatives of the joint flow
  have hFt : ∀ (u' : ℝ) (y : Vec 2), fderiv ℝ F (u', y) (1, 0) =
      streamVel (D.Φ (m - 1)) u' (F (u', y)) := by
    intro u' y
    have h1 := (hFd (u', y)).hasFDerivAt.comp_hasDerivAt u'
      ((hasDerivAt_id u').prodMk (hasDerivAt_const u' y))
    exact h1.unique (hflow.2 y s u')
  have hFy : ∀ (u' : ℝ) (y V : Vec 2), fderiv ℝ F (u', y) (0, V) =
      fderiv ℝ (fun z => D.flowOf (m - 1) u' z s) y V := by
    intro u' y V
    have h1 : HasFDerivAt (fun z : Vec 2 => F (u', z))
        ((fderiv ℝ F (u', y)).comp ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))))
        y :=
      (hFd (u', y)).hasFDerivAt.comp y ((hasFDerivAt_const u' y).prodMk (hasFDerivAt_id y))
    have h2 := h1.fderiv
    change fderiv ℝ (fun z => D.flowOf (m - 1) u' z s) y = _ at h2
    rw [h2]
    simp
  have hγ : ∀ u' ∈ Set.uIcc r u, HasDerivAt γ (streamVel (D.Φ m) u' (γ u')) u' := by
    intro u' hu'
    have h1 := (hFd (u', W u')).hasFDerivAt.comp_hasDerivAt u'
      ((hasDerivAt_id u').prodMk (hW u'))
    have hsplit : ((1 : ℝ), ocPulse D.α D.q D.Λ D.ζ m p u' • U) =
        ((1 : ℝ), (0 : Vec 2)) + ((0 : ℝ), ocPulse D.α D.q D.Λ D.ζ m p u' • U) := by simp
    have hlabel : D.flowOf (m - 1) s (γ u') u' = W u' := flowOf_inv D (m - 1) s u' (W u')
    have hshear : ocShearVel D.α D.q D.Λ m p (W u') = U :=
      ChainGeometry.ocShearVel_add_smul_self D.α D.q D.Λ m p w w _
    have hvel := hsp u' hu' (γ u')
    rw [hlabel, hshear] at hvel
    rw [hvel]
    rw [hsplit, map_add, hFt, hFy, map_smul] at h1
    exact h1
  have hη : ∀ u', HasDerivAt η (streamVel (D.Φ m) u' (η u')) u' := fun u' => hflowm.2 x r u'
  have h0 : γ r = η r := by
    show D.flowOf (m - 1) r (w + (∫ v in r..r, ocPulse D.α D.q D.Λ D.ζ m p v) • U) s =
      D.flowOf m r x r
    rw [intervalIntegral.integral_same, zero_smul, add_zero, hw, flowOf_inv,
      Providers.QuietAtlas.flowOf_self]
  -- uniqueness of the integral curve on the interval between `r` and `u`
  obtain ⟨L, hL⟩ := (D.hΦ m).vel_lipschitz
  have hLip := AVenhance.Infra.Flow.lipschitzWith_of_uniform_bound (streamVel (D.Φ m)) hL
  suffices hfin : γ u = η u from hfin.symm
  rcases le_total r u with hru | hur
  · have hI : Set.Icc r u = Set.uIcc r u := (Set.uIcc_of_le hru).symm
    exact ODE_solution_unique_of_mem_Icc_right (v := streamVel (D.Φ m)) (s := fun _ => Set.univ)
      (fun t _ => (hLip t).lipschitzOnWith)
      (fun t ht => (hγ t (hI ▸ ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hγ t (hI ▸ Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun _ _ => Set.mem_univ _)
      (fun t _ => (hη t).continuousAt.continuousWithinAt)
      (fun t _ => (hη t).hasDerivWithinAt) (fun _ _ => Set.mem_univ _) h0
      (Set.right_mem_Icc.mpr hru)
  · have hI : Set.Icc u r = Set.uIcc r u := (Set.uIcc_of_ge hur).symm
    exact ODE_solution_unique_of_mem_Icc_left (v := streamVel (D.Φ m)) (s := fun _ => Set.univ)
      (fun t _ => (hLip t).lipschitzOnWith)
      (fun t ht => (hγ t (hI ▸ ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hγ t (hI ▸ Set.Ioc_subset_Icc_self ht)).hasDerivWithinAt)
      (fun _ _ => Set.mem_univ _)
      (fun t _ => (hη t).continuousAt.continuousWithinAt)
      (fun t _ => (hη t).hasDerivWithinAt) (fun _ _ => Set.mem_univ _) h0
      (Set.left_mem_Icc.mpr hur)

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! Transfer collapse, the geometry of the appended child. The coarser slot
`p` has level `m`, the finer slot `k` level `m + 1`.

For the native context of `p` at the base label `X`, the child appended for `k` at the time `t`
and the phase `X/ε_m` (the phase at which `transferAt` reads it from `constituentPhysical`) has
* the anchor `s_k`, and the offset flow `X_m` between two times of a single pulse `p`
  (`tc_appendChild_flow`, from `flowOf_single_pulse`: the relative phase of the child vanishes);
* the centre point `φ(X) = X_m(s_k, X_{m-1}(t, X, s_p), t)`, the finer label of the physical point
  of the coarse label `X` at the time `t` (`tc_appendChild_center`).
Hence it has the history geometry of the finer native family recentred at `φ(X)` on every set of
times joined to `s_k` by single-pulse intervals (`tc_appendChild_histEq`), and its transfer
Jacobian is the inverse Jacobian of the label change `φ` (`tc_childTransition_inv`). On a quiet
history these are `appendChild_geom_quiet`, `childTransition_inv_native`; here the pulse `p` may
act between `t` and `s_k`. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Providers.QuietAtlas

variable {D : OCData}

/-- The label change from the chart of the coarser slot `p` (level `m`) to the chart of the finer
slot `k` (level `m + 1`) at the time `t`. -/
def labelChange (D : OCData) (m : ℕ) (p k : ℤ) (t : ℝ) : Vec 2 → Vec 2 :=
  fun Y => D.flowOf m (D.slotAnchor (m + 1) k) (D.flowOf (m - 1) t Y (D.slotAnchor m p)) t

/-- The inverse label change. -/
def labelChangeInv (D : OCData) (m : ℕ) (p k : ℤ) (t : ℝ) : Vec 2 → Vec 2 :=
  fun Y => D.flowOf (m - 1) (D.slotAnchor m p) (D.flowOf m t Y (D.slotAnchor (m + 1) k)) t

theorem labelChange_inv (D : OCData) (m : ℕ) (p k : ℤ) (t : ℝ) (Y : Vec 2) :
    labelChangeInv D m p k t (labelChange D m p k t Y) = Y := by
  simp only [labelChange, labelChangeInv, flowOf_inv]

theorem labelChangeInv_inv (D : OCData) (m : ℕ) (p k : ℤ) (t : ℝ) (Y : Vec 2) :
    labelChange D m p k t (labelChangeInv D m p k t Y) = Y := by
  simp only [labelChange, labelChangeInv, flowOf_inv]

theorem contDiff_labelChange (D : OCData) (m : ℕ) (p k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (labelChange D m p k t) :=
  (flowOf_contDiff D m _ _).comp (flowOf_contDiff D (m - 1) _ _)

theorem contDiff_labelChangeInv (D : OCData) (m : ℕ) (p k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (labelChangeInv D m p k t) :=
  (flowOf_contDiff D (m - 1) _ _).comp (flowOf_contDiff D m _ _)

/-- The finer natural chart after the label change is the coarser natural chart. -/
theorem flowOf_labelChange (D : OCData) (m : ℕ) (p k : ℤ) (t : ℝ) (Y : Vec 2) :
    D.flowOf m t (labelChange D m p k t Y) (D.slotAnchor (m + 1) k) =
      D.flowOf (m - 1) t Y (D.slotAnchor m p) := by
  simp only [labelChange, flowOf_inv]

/-- The geometry of the child appended to the native context of `p` at the label `X`, at the
phase `X/ε_m`. -/
theorem tc_appendChild_geom {m : ℕ} (hm : 1 ≤ m) (p k : ℤ) (t : ℝ) (X : Vec 2) :
    ((⟨m - 1, [p], X, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • X)).geom D =
      D.childGeom m p (D.slotAnchor (m + 1) k)
        ⟨D.eps m • D.relDisp m p (D.slotAnchor (m + 1) k) t ((D.eps m)⁻¹ • X),
          (D.eps m)⁻¹ • X + D.relDisp m p (D.slotAnchor (m + 1) k) t ((D.eps m)⁻¹ • X)⟩
        (D.flowOf (m - 1), X, D.slotAnchor m p) := by
  have hctx : (⟨m - 1, [p], X, []⟩ : RealChain).ctxLevel = m := by
    show m - 1 + 0 + 1 = m
    omega
  have hslot : (⟨m - 1, [p], X, []⟩ : RealChain).slot = p := rfl
  have hl : (⟨m - 1, [p], X, []⟩ : RealChain).WellSlotted := rfl
  rw [Providers.GenSem.appendChild_geom D _ hl, hctx, hslot, StrainPhysical.geom_native D m hm p X]

theorem tc_appendChild_anchor {m : ℕ} (hm : 1 ≤ m) (p k : ℤ) (t : ℝ) (X : Vec 2) :
    (((⟨m - 1, [p], X, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • X)).geom D).2.2 =
      D.slotAnchor (m + 1) k := by
  rw [tc_appendChild_geom hm]
  rfl

/-- The offset flow of the appended child: the flow of level `m - 1` after the shear displacement
of the pulse `p` in the labels of its anchor. -/
theorem tc_appendChild_flow_formula {m : ℕ} (hm : 1 ≤ m) (hε : D.eps m ≠ 0) (p k : ℤ) (t : ℝ)
    (X : Vec 2) (u : ℝ) (x : Vec 2) (r : ℝ) :
    (((⟨m - 1, [p], X, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • X)).geom D).1 u x r =
      D.flowOf (m - 1) u
        (D.flowOf (m - 1) (D.slotAnchor m p) x r +
          (∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ m p v) •
            ocShearVel D.α D.q D.Λ m p (D.flowOf (m - 1) (D.slotAnchor m p) x r))
        (D.slotAnchor m p) := by
  rw [tc_appendChild_geom hm]
  have hphase : (D.eps m)⁻¹ • X + D.relDisp m p (D.slotAnchor (m + 1) k) t ((D.eps m)⁻¹ • X) -
      (D.eps m)⁻¹ • (X + D.eps m • D.relDisp m p (D.slotAnchor (m + 1) k) t ((D.eps m)⁻¹ • X)) =
      0 := by
    rw [smul_add, inv_smul_smul₀ hε]
    abel
  simp only [OCData.childGeom, hphase, add_zero]
  simp only [OCData.relDisp, smul_inv_smul₀ hε]

/-- **The offset flow of the appended child is the flow of level `m`** between two times of a
single pulse `p`. -/
theorem tc_appendChild_flow (hζ : IsFastProfile D.ζ) {m : ℕ} (hm : 1 ≤ m) (hε : D.eps m ≠ 0)
    (p k : ℤ) (t : ℝ) (X : Vec 2) {u r : ℝ} (hsp : ∀ v ∈ Set.uIcc r u, SinglePulseAt D m p v)
    (x : Vec 2) :
    (((⟨m - 1, [p], X, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • X)).geom D).1 u x r =
      D.flowOf m u x r := by
  rw [tc_appendChild_flow_formula hm hε, flowOf_single_pulse hζ hsp x]

/-- **The centre point of the appended child is the finer label** of the physical point. -/
theorem tc_appendChild_center (hζ : IsFastProfile D.ζ) {m : ℕ} (hm : 1 ≤ m) (hε : D.eps m ≠ 0)
    (p k : ℤ) (t : ℝ) (X : Vec 2)
    (hsp : ∀ v ∈ Set.uIcc t (D.slotAnchor (m + 1) k), SinglePulseAt D m p v) :
    (((⟨m - 1, [p], X, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • X)).geom D).2.1 =
      labelChange D m p k t X := by
  rw [tc_appendChild_geom hm]
  unfold labelChange
  rw [flowOf_single_pulse hζ hsp, flowOf_inv]
  simp only [OCData.childGeom, OCData.relDisp, smul_inv_smul₀ hε]

/-- **The appended child has the history geometry of the recentred finer native family**, on
every set of times joined to the finer anchor by single-pulse intervals. -/
theorem tc_appendChild_histEq (hζ : IsFastProfile D.ζ) {m : ℕ} (hm : 1 ≤ m) (hε : D.eps m ≠ 0)
    (p k : ℤ) (t : ℝ) (X : Vec 2) {I : Set ℝ}
    (hI : ∀ u ∈ I, ∀ v ∈ Set.uIcc (D.slotAnchor (m + 1) k) u, SinglePulseAt D m p v)
    (ht : ∀ v ∈ Set.uIcc t (D.slotAnchor (m + 1) k), SinglePulseAt D m p v) :
    HistEq (((⟨m - 1, [p], X, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • X)).geom D)
      ((⟨m, [k], labelChange D m p k t X, []⟩ : RealChain).geom D) I := by
  have hnat : (⟨m, [k], labelChange D m p k t X, []⟩ : RealChain).geom D =
      (D.flowOf m, labelChange D m p k t X, D.slotAnchor (m + 1) k) := by
    simp [RealChain.geom, OCData.geomAux]
  rw [hnat]
  refine ⟨tc_appendChild_anchor hm p k t X, fun u hu h => ?_⟩
  rw [tc_appendChild_anchor hm, tc_appendChild_center hζ hm hε p k t X ht]
  exact tc_appendChild_flow hζ hm hε p k t X (hI u hu) _

/-- **The transfer Jacobian of the native context is the inverse Jacobian of the label change.**
-/
theorem tc_childTransition_inv (hζ : IsFastProfile D.ζ) {m : ℕ} (hm : 1 ≤ m) (hε : D.eps m ≠ 0)
    (p k : ℤ) (t : ℝ) (X : Vec 2)
    (hsp : ∀ v ∈ Set.uIcc t (D.slotAnchor (m + 1) k), SinglePulseAt D m p v) :
    (childTransition D k t ⟨m - 1, [p], X, []⟩ ((D.eps m)⁻¹ • X))⁻¹ =
      chartInvJacobian (labelChange D m p k t) X := by
  set c : RealChain := ⟨m - 1, [p], X, []⟩ with hc
  set sk := D.slotAnchor (m + 1) k with hsk
  have hgeom : c.geom D = (D.flowOf (m - 1), X, D.slotAnchor m p) :=
    StrainPhysical.geom_native D m hm p X
  have hF : c.famJac D t = jacMatrix (fun y => D.flowOf (m - 1) t y (D.slotAnchor m p)) X := by
    unfold RealChain.famJac
    rw [hgeom]
  have hFa : (c.appendChild D k t ((D.eps m)⁻¹ • X)).famJac D t =
      jacMatrix (fun y => D.flowOf m t y sk) (labelChange D m p k t X) := by
    unfold RealChain.famJac
    rw [tc_appendChild_anchor hm, tc_appendChild_center hζ hm hε p k t X hsp]
    congr 1
    funext y
    exact tc_appendChild_flow hζ hm hε p k t X (by rw [Set.uIcc_comm]; exact hsp) y
  have hcomp : (fun y => D.flowOf (m - 1) t y (D.slotAnchor m p)) =
      (fun y => D.flowOf m t y sk) ∘ labelChange D m p k t := by
    funext y
    exact (flowOf_labelChange D m p k t y).symm
  have hJ := CycleReference.jacMatrix_comp (f := fun y => D.flowOf m t y sk)
    (g := labelChange D m p k t) X
    ((flowOf_contDiff D _ _ _).differentiable (by simp) _)
    ((contDiff_labelChange D m p k t).differentiable (by simp) _)
  have hunit : IsUnit (jacMatrix (fun y => D.flowOf m t y sk) (labelChange D m p k t X)).det := by
    rw [flowOf_det]
    exact isUnit_one
  unfold childTransition
  rw [hF, hFa, hcomp, hJ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
  rfl

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The fluxes of the retained readout flux cancellation.

With `Z = 𝖱Y` (classical representative `aZ`) and the retained solution `Y` (representative `aY`):

* `R = 𝖱Π𝖠^S Y`: the readout of the kernel flux of the retained family (retained rows, retained
  columns);
* `RO = 𝖱F_om`: the readout of `𝖠^S Y` on the omitted rows only;
* `K = ∑ 𝖮_γ S_γ Z + ∑ 𝖥_{𝔩,γ} S_m Z`, `Pl = (𝖮 + ∑ 𝖥_𝔩)Z`, `RD = ∑ 𝖮_γ(I - S_γ)Z +
  ∑ 𝖥_{𝔩,γ}(I - S_m)Z`: the readouts, over **all** rows of the extended successor `G'`, of the
  fluxes of the identities of `G'` out of the incoming components (the roots `(u, ∅)`), in the
  kernel, plain and defect modes (`rootFluxOn`). These are coefficients of the **successor** (level
  `m - 1`), not of the incoming family: `coeffFluxOn … G` (the level-`m` coefficients `𝖠_m`) acts
  only on the lifted field `TP_pZ`.
* `N = Q_p G`, `G = (𝒟 - 𝐄^flux P_p)Z`.

Pointwise `R = K - RO` and `K = Pl - RD`, and `Pl = -N` (after testing) is the split of the
core `SuccessorSplitCoreStatement` below. In the degenerate case `J = 0`, every letter row is
omitted, so `RO = ∑ 𝖥 S_m Z` is the whole fresh kernel term and `R = ∑ 𝖮 S Z`; `RD` does not
vanish. An incoming component with no
incoming identity still has the first-source letter in `K`, `Pl` and `RD` (it is an identity of
`G'`, not of `G`).

The fluxes are evaluated on the `CovarianceTransport.Frame`, so that the quantifier prefix of
the statement is not copied. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The flux `∑_{u,γ,d} 𝖡_{γ,d}(t,x) ∇^{d-1}(K_γ g_u)` of the identities of the extended successor
`G'` out of the incoming components (the roots `(u, ∅)`, `u ∈ G.comps`) into the component `v'`
of `G'`, on a classical field `g` on the incoming components, with `K_γ = I`, `S_γ` or `I - S_γ`
according to the mode. In the mode `.defect` this is `rootFluxDefect`. -/
def rootFluxOn (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' : GenStage D hr Dm b j₀) (mode : KerMode)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v' : CompIn G'.comps) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v'.1.root) :=
  ∑ u' : CompIn G'.comps, if hu : u'.1 ∈ G.comps then
    ∑ γ : G'.fam.Γ v' u', ∑ d : Finset.Icc 2 Dm,
      G'.physCoeff v' u' γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word (fun y =>
          match mode with
          | .plain => g t y ⟨u'.1, hu⟩
          | .kernel => (G'.kernelOf P seedK freshK v' u' γ).applyClassical φ₀ t
              (fun y' => g t y' ⟨u'.1, hu⟩) y
          | .defect => g t y ⟨u'.1, hu⟩ -
              (G'.kernelOf P seedK freshK v' u' γ).applyClassical φ₀ t
                (fun y' => g t y' ⟨u'.1, hu⟩) y) x)
    else 0

/-- The readout, over all rows of `G'`, of the flux out of the roots in the given mode, into the
incoming components: the passage level is `m`, the readout weights are `E^{η|𝔱|}`. -/
def rootReadout (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' : GenStage D hr Dm b j₀) (mode : KerMode) (m : ℕ) (E η : ℝ)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    ∀ v : CompIn G.comps, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  readoutFlux m E η (fun _ => True)
    (fun v' s y => rootFluxOn P seedK freshK φ₀ G G' mode g v' s y)

variable (F : Frame D hr Dm b j₀)

/-- `R`: the readout of the kernel flux of the retained family on the retained solution. -/
def fluxR : F.Flux := fun v =>
  readoutFlux F.m (D.eps (F.m - 1)) F.η₀ (fun _ => True)
    (fun v' s y => coeffFluxOn F.P F.seedK F.freshK F.φ₀ F.Gr .kernel F.aY v' s y) v

/-- `RO`: the readout of the omitted flux `(I - Π)𝖠^S Y`, on the omitted rows only. -/
def fluxRO : F.Flux := fun v t x =>
  readoutFlux F.m (D.eps (F.m - 1)) F.η₀ (fun c => ¬ IsRetained F.m F.H F.J c)
    (fun v' s y => omittedFluxClassical F.P F.seedK F.freshK F.φ₀ F.G' F.Gr F.aY v' s y) v t x

/-- `RD`: the readout of the root defect fluxes of the extended successor, all rows. -/
def fluxRD : F.Flux := fun v t x =>
  readoutFlux F.m (D.eps (F.m - 1)) F.η₀ (fun _ => True)
    (fun v' s y => rootFluxDefect F.P F.seedK F.freshK F.φ₀ F.G F.G' F.aZ v' s y) v t x

/-- `K = ∑ 𝖮_γ S_γ Z + ∑ 𝖥_{𝔩,γ} S_m Z`: the kernel flux of the successor out of the roots. -/
def fluxK : F.Flux :=
  rootReadout F.P F.seedK F.freshK F.φ₀ F.G F.G' .kernel F.m (D.eps (F.m - 1)) F.η₀ F.aZ

/-- `Pl = (𝖮 + ∑ 𝖥_𝔩)Z`: the plain flux of the successor out of the roots. -/
def fluxPl : F.Flux :=
  rootReadout F.P F.seedK F.freshK F.φ₀ F.G F.G' .plain F.m (D.eps (F.m - 1)) F.η₀ F.aZ

/-- `N = Q_p G`, `G = menuGFlux`, as a `PiLp` field, at the menu `Mn` (anchor and slow length of
the menu; the cascade has anchor `0` and factor `1`, the terminal passage `t_p` and `c_r`). -/
def menuCovFlux (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  toFluxL (covPolyQ (menuCovPrimitive D Mn m t) p
    (fun y => menuGFlux Mn G m N p depth CcT a v t y) x)

/-- `N = Q_p G`, `G = (𝒟 - 𝐄^flux P_p)Z`, as a `PiLp` field of the frame's menu. -/
def fluxN : F.Flux := fun v t x =>
  menuCovFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t x

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end

section
/-! The steps of the retained readout flux cancellation, as predicates on the
`CovarianceTransport.Frame`. With the fluxes `fluxR`, `fluxRO`, `fluxRD`, `fluxK`, `fluxPl`,
`fluxN` above:

* `ReindexOn`: `R = K - RO` pointwise (provenance reindexing of the rows of the extended successor
  to the incoming components; the omitted rows supply exactly what the retained rows miss);
* `KernelSplitOn`: `K = Pl - RD` pointwise (`S = I - (I - S)` under ordered derivatives);
* `ReconstructOn`: `Pl ~ -N` after testing (the split of the core on `Z`);
* `FluxContinuityOn`: spatial continuity of `R, RO, RD, Pl, N` at every time of the window;
* `CancellationOn`: the conclusion `R ~ -(N + (RD + RO))`.

`cancellationOn_of_steps` chains them on one frame. There is no root-defect step: the defect flux
of the chain is literally `RD`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

section Tested
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Subtracting a flux with integrable gradient pairing from both sides of a tested agreement. -/
theorem testedFlux_sub_common {μ : Measure (Vec 2)} {W : Set ℝ}
    {Q₁ Q₂ C : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} {dφ : Fin 2 → Vec 2 → E}
    (h : TestedFluxAgreement μ W Q₁ Q₂ dφ)
    (hC : ∀ s ∈ W, Integrable (fun x => ∑ j : Fin 2, inner ℝ (C s x j) (dφ j x)) μ) :
    TestedFluxAgreement μ W (fun s x => Q₁ s x - C s x) (fun s x => Q₂ s x - C s x) dφ := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := h s hs
  have e1 : ∀ x, ∑ j : Fin 2, inner ℝ ((Q₁ s x - C s x) j) (dφ j x) =
      (∑ j : Fin 2, inner ℝ (Q₁ s x j) (dφ j x)) - ∑ j : Fin 2, inner ℝ (C s x j) (dφ j x) := by
    intro x
    simp only [PiLp.sub_apply, inner_sub_left, Finset.sum_sub_distrib]
  have e2 : ∀ x, ∑ j : Fin 2, inner ℝ ((Q₂ s x - C s x) j) (dφ j x) =
      (∑ j : Fin 2, inner ℝ (Q₂ s x j) (dφ j x)) - ∑ j : Fin 2, inner ℝ (C s x j) (dφ j x) := by
    intro x
    simp only [PiLp.sub_apply, inner_sub_left, Finset.sum_sub_distrib]
  refine ⟨(h1.sub (hC s hs)).congr (Filter.Eventually.of_forall fun x => (e1 x).symm),
    (h2.sub (hC s hs)).congr (Filter.Eventually.of_forall fun x => (e2 x).symm), ?_⟩
  calc (∫ x, ∑ j : Fin 2, inner ℝ ((Q₁ s x - C s x) j) (dφ j x) ∂μ)
      = ∫ x, (∑ j : Fin 2, inner ℝ (Q₁ s x j) (dφ j x)) -
          ∑ j : Fin 2, inner ℝ (C s x j) (dφ j x) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall e1)
    _ = (∫ x, ∑ j : Fin 2, inner ℝ (Q₁ s x j) (dφ j x) ∂μ) -
          ∫ x, ∑ j : Fin 2, inner ℝ (C s x j) (dφ j x) ∂μ := integral_sub h1 (hC s hs)
    _ = (∫ x, ∑ j : Fin 2, inner ℝ (Q₂ s x j) (dφ j x) ∂μ) -
          ∫ x, ∑ j : Fin 2, inner ℝ (C s x j) (dφ j x) ∂μ := by rw [h3]
    _ = ∫ x, (∑ j : Fin 2, inner ℝ (Q₂ s x j) (dφ j x)) -
          ∑ j : Fin 2, inner ℝ (C s x j) (dφ j x) ∂μ := (integral_sub h2 (hC s hs)).symm
    _ = ∫ x, ∑ j : Fin 2, inner ℝ ((Q₂ s x - C s x) j) (dφ j x) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (e2 x).symm)

/-- A tested agreement only sees the fluxes on its time set. -/
theorem testedFlux_congr {μ : Measure (Vec 2)} {W : Set ℝ}
    {Q₁ Q₂ Q₁' Q₂' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} {dφ : Fin 2 → Vec 2 → E}
    (h : TestedFluxAgreement μ W Q₁ Q₂ dφ) (h1 : ∀ s ∈ W, ∀ x, Q₁' s x = Q₁ s x)
    (h2 : ∀ s ∈ W, ∀ x, Q₂' s x = Q₂ s x) : TestedFluxAgreement μ W Q₁' Q₂' dφ := by
  intro s hs
  have e1 : (fun x => ∑ j : Fin 2, inner ℝ (Q₁' s x j) (dφ j x)) =
      fun x => ∑ j : Fin 2, inner ℝ (Q₁ s x j) (dφ j x) := by
    funext x
    rw [h1 s hs x]
  have e2 : (fun x => ∑ j : Fin 2, inner ℝ (Q₂' s x j) (dφ j x)) =
      fun x => ∑ j : Fin 2, inner ℝ (Q₂ s x j) (dφ j x) := by
    funext x
    rw [h2 s hs x]
  rw [e1, e2]
  exact h s hs

/-- Pointwise equal fluxes with one integrable gradient pairing agree after testing. -/
theorem testedFlux_of_pointwise {μ : Measure (Vec 2)} {W : Set ℝ}
    {Q₁ Q₂ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} {dφ : Fin 2 → Vec 2 → E}
    (heq : ∀ s ∈ W, ∀ x, Q₁ s x = Q₂ s x)
    (hint : ∀ s ∈ W, Integrable (fun x => ∑ j : Fin 2, inner ℝ (Q₂ s x j) (dφ j x)) μ) :
    TestedFluxAgreement μ W Q₁ Q₂ dφ := by
  intro s hs
  have e : (fun x => ∑ j : Fin 2, inner ℝ (Q₁ s x j) (dφ j x)) =
      fun x => ∑ j : Fin 2, inner ℝ (Q₂ s x j) (dφ j x) := by
    funext x
    rw [heq s hs x]
  rw [e]
  exact ⟨hint s hs, hint s hs, rfl⟩

/-- A spatially continuous flux has an integrable pairing with the gradient of a smooth test on
the unit cell. -/
theorem fluxPairing_integrable {A : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} (hA : Continuous A)
    {φ : Vec 2 → E} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Integrable (fun x => ∑ j : Fin 2, inner ℝ (A x j) (gradE φ x j))
      (volume.restrict AVenhance.unitCube) := by
  have htest (j : Fin 2) : Continuous (fun x => gradE φ x j) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc : Continuous (fun x => ∑ j : Fin 2, inner ℝ (A x j) (gradE φ x j)) :=
    continuous_finsetSum _ fun j _ => ((PiLp.continuous_apply 2 _ j).comp hA).inner (htest j)
  have : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact (measure_mono AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra.weakUnitCube_subset_closedCell).trans_lt
          AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra.weakSpatialClosedCell_compact.measure_lt_top⟩
  exact (CycleComparison.Lift.continuous_cell_memLp _ hc).integrable (by norm_num)

end Tested

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Agreement of two fluxes of a frame after testing against `∇φ`, for every incoming component,
every time of the window and every smooth periodic test; each side is integrable against `∇φ`
at every time (part of `TestedFluxAgreement`), and no gauge is fixed. -/
def TestedOn (F : Frame D hr Dm b j₀) (A B : F.Flux) : Prop :=
  ∀ v : CompIn F.G.comps, ∀ t ∈ Set.Icc F.tp F.tf, ∀ φ : Vec 2 → hr v.1.root,
    ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
    TestedFluxAgreement (volume.restrict AVenhance.unitCube) (Set.Ioc F.tp t) (A v) (B v)
      (fun j x => gradE φ x j)

/-- (a)+(d) `R = K - RO`, pointwise on the window: the rows of the extended successor with parent
`v` are the retained rows (in `R`) and the omitted rows (in `RO`); by the source bijection of
`IsActualSuccessor` a copy is the same operator in every word and a letter carries `E^{-η₀}`, so
the word sums rebuild `Z`. -/
def ReindexOn (F : Frame D hr Dm b j₀) : Prop :=
  ∀ v : CompIn F.G.comps, ∀ t ∈ Set.Icc F.tp F.tf, ∀ x : Vec 2,
    fluxR F v t x = fluxK F v t x - fluxRO F v t x

/-- (c) `K = Pl - RD`, pointwise on the window: `S_γ = I - (I - S_γ)` under the ordered
derivatives of the successor identities out of the roots. -/
def KernelSplitOn (F : Frame D hr Dm b j₀) : Prop :=
  ∀ v : CompIn F.G.comps, ∀ t ∈ Set.Icc F.tp F.tf, ∀ x : Vec 2,
    fluxK F v t x = fluxPl F v t x - fluxRD F v t x

/-- (b) `Pl ~ -N` after testing: the split of the core on the readout `Z`. -/
def ReconstructOn (F : Frame D hr Dm b j₀) : Prop :=
  TestedOn F (fluxPl F) (fun v t x => -fluxN F v t x)

/-- Spatial continuity of the five fluxes at every time of the window (hence integrability of
their gradient pairings on the unit cell). -/
def FluxContinuityOn (F : Frame D hr Dm b j₀) : Prop :=
  ∀ v : CompIn F.G.comps, ∀ t ∈ Set.Icc F.tp F.tf,
    Continuous (fluxR F v t) ∧ Continuous (fluxRO F v t) ∧ Continuous (fluxRD F v t) ∧
      Continuous (fluxPl F v t) ∧ Continuous (fluxN F v t)

/-- The tested cancellation `R ~ -(Q_p G + Υ)` on a frame. -/
def CancellationOn (F : Frame D hr Dm b j₀) : Prop :=
  TestedOn F (fluxR F) F.readFlux

/-- The chain `R = K - RO = (Pl - RD) - RO ~ (-N - RD) - RO = -(N + (RD + RO))` on one frame.
Only the integrability of the pairing of `RD + RO` is taken from the continuity statement; that
of `Pl` and `N` is part of the tested core. -/
theorem cancellationOn_of_steps (F : Frame D hr Dm b j₀) (h1 : ReindexOn F)
    (h2 : KernelSplitOn F) (h3 : ReconstructOn F) (hc : FluxContinuityOn F) :
    CancellationOn F := by
  intro v t ht φ hφ hp
  have hsub : ∀ s ∈ Set.Ioc F.tp t, s ∈ Set.Icc F.tp F.tf :=
    fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hU : ∀ s ∈ Set.Ioc F.tp t, Integrable (fun x => ∑ j : Fin 2,
      inner ℝ ((fluxRD F v s x + fluxRO F v s x) j) (gradE φ x j))
      (volume.restrict AVenhance.unitCube) := fun s hs =>
    fluxPairing_integrable ((hc v s (hsub s hs)).2.2.1.add (hc v s (hsub s hs)).2.1) hφ
  have h := testedFlux_sub_common (C := fun s x => fluxRD F v s x + fluxRO F v s x)
    (h3 v t ht φ hφ hp) hU
  refine testedFlux_congr h ?_ ?_
  · intro s hs x
    show fluxR F v s x = fluxPl F v s x - (fluxRD F v s x + fluxRO F v s x)
    rw [h1 v s (hsub s hs) x, h2 v s (hsub s hs) x]
    abel
  · intro s hs x
    show -(fluxN F v s x + (fluxRD F v s x + fluxRO F v s x)) =
      -fluxN F v s x - (fluxRD F v s x + fluxRO F v s x)
    abel

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual
open FluxCancellation CovarianceTransport

/-- (a)+(d) Provenance reindexing of the retained readout flux with the omitted-row correction,
`R = K - RO` pointwise, under the prefix. The proof is finite
bookkeeping over the source bijection of `IsActualSuccessor`, `compParent`, `compWord`, the casts
of `readoutFlux`, linearity of the kernel average and of ordered derivatives on `C^{Naux}`
fields. For `J = 0` all letter rows are omitted, so `RO = ∑ 𝖥 S_m Z` and `R = ∑ 𝖮 S Z`; for one
component without incoming identity `K` is the first-source letter on `S_m Z`. -/
def RetainedReadoutReindexStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  CovarianceTransportProductionStatement α s q ζ ReindexOn

/-- (c) Kernel split `K = Pl - RD` pointwise, under the prefix. The proof takes
`orderedDerivative` of a difference of `C^{Dm-1}` fields; the kernel average of a
`C^k` periodic field is `C^k` (`kernel_readout_kernel_classical_rep`). -/
def RetainedReadoutKernelSplitStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  CovarianceTransportProductionStatement α s q ζ KernelSplitOn

/-- Spatial continuity of `R, RO, RD, Pl, N` at every time of the window, under the
prefix. For `R` use `kernel_readout_flux_continuous` with the retained
certificates. `RO, RD, Pl`: the same argument with the
coefficients of the extended successor on all rows (`extended_successor_context_certified`,
`native_physCoeff_all_order_smooth`). `N`: the regularity piece of the core (no lemma on
`gluedMeanFlux` exists yet). The assembly consumes only `RD` and `RO`. -/
def RetainedReadoutFluxContinuityStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  CovarianceTransportProductionStatement α s q ζ FluxContinuityOn

end AVRegularity.Construction.Preservation.Residual
end
end

section
/-! The core of the flux cancellation: the split
`(𝖮 + ∑_𝔩 𝖥_𝔩) g = -Q_p(𝒟 - 𝐄^flux P_p) g`
as an identity of flux operators on an **arbitrary** classical periodic field `g`, generic over
the stage and the menu: it involves neither the retained solution,
nor the kernels, nor the preparation, nor the omitted rows.

The right-hand side of the statement is written with the covariance flux `menuCovFlux` of the
menu, at its covariance anchor `s₀` and slow length `ρ`; the cascade's menu has `s₀ = 0` and
`ρ = liftLength D m`. The terminal passage is the instance
`s₀ = t_p`, `ρ = c_r · liftLength D M` (`termCovPrimitive`, `termLiftedRep`).

`SplitInput` lists what the identity uses of the stage. Its field `range` contains the two range
conditions:
* the alphabet is `succAlphabet nMax hMax p npad` and every flux array of the incoming stage
  vanishes above an order `Dord` with `N + Dord ≤ nMax`: the means of degree `n > N + Dord` then
  vanish (`C_n = 0` for `n > N`), so the degrees `N + Dord < n ≤ N + Dm` of `meanFluxE` need no
  letter. The bound is on the **arrays**, not on the recorded `maxOrder`: after one passage the
  letters of a cascade stage have `maxOrder` up to `N + D_H + 4p > D_H` (`letterOrder`), while their
  arrays into a component of grade `g` vanish above `D_g` (`cascadeFluxOrderBound`);
* every path has at most `min hMax depth` edges (proved for the cascade:
  `Providers.CascadeInvariants.cascade_path_length_le_of_generatedSeed`). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The flux coefficients of the actual contexts of `G` are jointly smooth in `(X, z)` at the times of
the pulse windows (the conclusion of `native_actual_flux_joint_contDiff`). Stated here because the
statement of the path-sum step uses it. -/
def CovFluxReg.ActualFluxJointSmooth (G : GenStage D hr Dm b j₀) : Prop :=
  ∀ (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1))
    (t : ℝ), t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 → ∀ n : ℕ,
    ContDiff ℝ (n : ℕ∞) (Function.uncurry (G.fam.flux p (G.actual p) v u γ d I t))

/-- What the split uses of an incoming stage `G`, its extended successor `G'` and the actual lift
`CcT` of `G` (the first clause of `IsLiftedField` / `IsTerminalLiftedField`), at the slow length
`ρ` and the covariance anchor `s₀` of the menu. See the module docstring for `range`; its last two
conjuncts are the lift reserves in the form of the cascade's floors (at the terminal menu the
floors are existential, and are chosen above these). Field `edge`: a context certificate of `G` with slot transversality and the reserve bounds
`0 ≤ compReserve k v ≤ 2` (joint smoothness of the flux coefficients of the incoming stage).
Field `stream`: the stream sequence is the constructed one, so that
the flow of level `m - 1` (the finer natural charts of `sourceEulerOp`) is the flow of level
`m - 2` after the pulses of level `m - 1` (the children read by `transferAt`).
Field `history`: the carried history invariant of the incoming stage
(clause 4 of `IsStageInvariant`); the old fluxes at the appended child of a coarser native
context and at the recentred finer native family agree because the two chains have the same
history geometry.
Field `start`: the carrier start at the constants `1, 1`
(admissibility of the appended children, and the availability interval of an active finer slot
lies where a single coarser pulse acts).
Conjunct `2 ≤ Dord` of `range`: the path means of the degrees
`n > N + max 2 Dord` vanish (one term of the lift flux needs `n - 2 > N` whatever the edges), and
the letters cover the degrees `n ≤ nMax`.
Fields `alpha_pos`, `q_gt`: the parameter range `0 < α`, `1 < q`
of the stream (hypotheses of `context_strain_physical`, used by the first source); no other field
constrains the sign of `α`. -/
structure SplitInput (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)) : Prop where
  stage : StageSuccessor.Input P Mn G
  successor : IsActualSuccessor D P Mn G G'
  lift : ∀ (k : ℤ) (hk : Odd k),
    IsLiftSequence (familyLiftData D G.level k (nativeChain G.level k) (Mn.lenFactor * liftLength D G.level)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N depth
      (CcT k)
  range : ∃ Dord nMax hMax npad : ℕ, Mn.A = succAlphabet nMax hMax Mn.p npad ∧
    Mn.N + Dord ≤ nMax ∧ 2 ≤ Dord ∧
    (∀ (p : OddSlot) (c : StageCtx D b j₀ G.level p) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ℕ) (I : DerivativeWord2 (d - 1)), Dord < d →
        G.fam.flux p c v u γ d I = fun _ _ _ => 0) ∧
    (∀ h, StagePath G h → h ≤ hMax ∧ h ≤ depth) ∧
    max (Mn.N + Dord) (2 * Mn.p) + Dm + 2 ≤ Mn.sX ∧
    max (Mn.N + Dord) (2 * Mn.p) + Dm + 2 ≤ Mn.sZ
  edge : ∃ k : InvConsts, G.IsContextCertified k ∧ G.IsSlotTransverse ∧
    ∀ v : CompIn G.comps, 0 ≤ compReserve k v.1 ∧ compReserve k v.1 ≤ 2
  stream : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ
  history : ∃ Mtop : ℕ, StageHistoryInvariant G Mtop
  start : IsCarrierStart D.α D.q D.Λ b 1 1 j₀
  alpha_pos : 0 < D.α
  q_gt : 1 < D.q

/-- **The split on a classical field** (generic over the stage and the menu). For a field `g` on
the incoming components which is `C^K` and periodic at every time of `[ta, tb]`,
`K ≥ N + Dm + 4p` (the largest order applied: `Q_p 𝐄^flux P_p`), the plain flux of the successor
out of the roots and `-Q_p G` agree after testing against the gradient of every smooth periodic
test, with integrable pairings at every time. No time window is tied to the stage: every
hypothesis is global in time, the cutoffs form a partition of unity at every real time
(`ocCutoff_finsum_one`), and a finer slot active at a time of a coarser window is scheduled in it
by definition (`IsScheduledIn`).
For a component without incoming identity the plain flux
is the first-source letter alone and `G = 𝒟 g`; for `g = 0` both sides vanish. The statement is
tested, not pointwise: the route through the pieces is pointwise, but only this form is consumed. -/
def SuccessorSplitCoreStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (K : ℕ), Mn.N + Dm + 4 * Mn.p ≤ K →
    ∀ (ta tb : ℝ) (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ∀ t ∈ Set.Icc ta tb,
        ContDiff ℝ (K : ℕ) (fun x => g t x v) ∧ IsZ2Periodic (fun x => g t x v)) →
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc ta tb, ∀ φ : Vec 2 → hr v.1.root,
      ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
      TestedFluxAgreement (volume.restrict AVenhance.unitCube) (Set.Ioc ta t)
        (rootReadout P seedK freshK φ₀ G G' .plain G.level (D.eps (G.level - 1)) Mn.η0 g v)
        (fun s x => -menuCovFlux Mn G G.level Mn.N Mn.p depth CcT g v s x)
        (fun j x => gradE φ x j)

/-- The hypotheses of the core on a frame of the quantifier prefix: the frame's own menu, whose
parameters are those of the frame (at the cascade, anchor `0` and slow length `liftLength D m`), and
the order of the readout representative. -/
def SplitInputOn (F : Frame D hr Dm b j₀) : Prop :=
  F.G.level = F.m ∧ F.Mn.N = F.N ∧ F.Mn.p = F.p ∧ F.Mn.η0 = F.η₀ ∧
    F.N + Dm + 4 * F.p ≤ F.Naux ∧
    SplitInput F.P F.Mn F.G F.G' F.depth F.CcT

/-- The reconstruct step for `aZ` is the core at `g = aZ`. -/
theorem reconstructOn_of_core (hcore : SuccessorSplitCoreStatement) (F : Frame D hr Dm b j₀)
    (hin : SplitInputOn F) : ReconstructOn F := by
  obtain ⟨hlev, hN, hp, hη, hK, hI⟩ := hin
  intro v t ht φ hφ hper
  have h := hcore F.P F.seedK F.freshK F.φ₀ F.Mn F.G F.G' F.depth F.CcT hI
    F.Naux (by rw [hN, hp]; exact hK) F.tp F.tf F.aZ
    (fun w s hs => ⟨(F.readout w s hs).2.1, (F.readout w s hs).2.2.1⟩) v t ht φ hφ hper
  rw [hlev, hN, hp, hη] at h
  exact h

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual
open FluxCancellation CovarianceTransport

/-- The cascade supplies the hypotheses of the core on every frame of the quantifier prefix, with
the menu `succMenu`. Its ingredients:
`StageSuccessor.cascade_successor_inputs` (the stage certificates), the successor and the lift
clause are binders of the prefix (`IsLiftedField`, first clause), `liftLength D m = 1 * liftLength
D G.level` and the anchor `0` by the definition of `succMenu`, the alphabet is
`succAlphabet (N + D_H) r_H p npad` by definition, the path bound is
`Providers.CascadeInvariants.cascade_path_length_le_of_generatedSeed`, the reserves are the two
floors of the prefix, `N + Dm + 4p ≤ Naux` is in `IsSuccessorSchedule`. The one new input is the
cascade flux order bound (`cascadeFluxOrderBound`) at `Dord = D_H`. -/
def CascadeSplitInputStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  CovarianceTransportProductionStatement α s q ζ SplitInputOn

end AVRegularity.Construction.Preservation.Residual
end
end
