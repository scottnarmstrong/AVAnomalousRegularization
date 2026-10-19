-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.ReconForceLimit
import AVRegularity.CycleComparison.Reconstruction.ReconForcePieces
import AVRegularity.CycleComparison.Reconstruction.LiftSource
public import AVRegularity.CycleComparison.Reconstruction.PartitionBound
public import AVRegularity.CycleComparison.Reconstruction.ReconLiftSlices
import AVRegularity.CycleComparison.Reconstruction.ReconForceCarrier
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.Weighted.MetricWordCoefficientArrayBound

@[expose] public noncomputable section

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The physical lift of the classical representative**. The glued lift of
`aRep`, clamped in time to the window (`obsGluedClamped`), is of class `C^{K_v+2}` and periodic in
every component at every time (`ReconWindowAt.gluedRep_smooth`), its jets of order `≤ K_v + 2` are
bounded on the window by a multiple of a bound of the norms of `W` (`ReconWindowAt.gluedRep_jet_le`),
and the jets of the difference with the glued lifts of the approximants are bounded by the Galerkin
errors of `W` (`ReconWindowAt.gluedApprox_sub_jet_le`). -/

section Defs

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

/-- The glued lift of the observed pulses, clamped in time to the window `[tA, tZ]`. -/
def obsGluedClamped (α q : ℝ) (Λ m : ℕ) (φs : ℝ → Vec 2 → ℝ) (hφs : IsAdmissibleStream φs)
    (ν B ρ tA tZ : ℝ) (htAZ : tA ≤ tZ) (ϖ : ℤ → ℝ → ℝ) (N H : ℕ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) :
    ∀ i, h i :=
  obsGlued α q Λ m φs hφs ν B ρ tA tZ ϖ N H Cc a (Set.projIcc tA tZ htAZ t) x

/-- On the window, the clamped glued lift is the glued lift. -/
theorem obsGluedClamped_of_mem (α q : ℝ) (Λ m : ℕ) (φs : ℝ → Vec 2 → ℝ)
    (hφs : IsAdmissibleStream φs) (ν B ρ tA tZ : ℝ) (htAZ : tA ≤ tZ) (ϖ : ℤ → ℝ → ℝ)
    (N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ}
    (ht : t ∈ Set.Icc tA tZ) (x : Vec 2) :
    obsGluedClamped α q Λ m φs hφs ν B ρ tA tZ htAZ ϖ N H Cc a t x =
      obsGlued α q Λ m φs hφs ν B ρ tA tZ ϖ N H Cc a t x := by
  unfold obsGluedClamped
  rw [projIcc_val_of_mem htAZ ht]

end Defs

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The clamped glued lift of the classical representative is smooth and periodic** in every
component at every time. -/
theorem ReconWindowAt.gluedRep_smooth
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Kmax : ℕ} (hKmax : ∀ v, K v ≤ Kmax) (hJK : Kmax + 2 ≤ Klift) (hJL : Kmax + 2 ≤ Llift)
    (hJr : Nc + (Kmax + 2) ≤ r₀)
    (t : ℝ) :
    (∀ v, ContDiff ℝ ((K v + 2 : ℕ) : ℕ∞) (fun x => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B
        ρ tp (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep t x v)) ∧
    (∀ v, IsZ2Periodic (fun x => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep t x v)) := by
  have htAZ : tp ≤ tp + Tobs := by linarith [w.hTobs]
  have hs : (Set.projIcc tp (tp + Tobs) htAZ t : ℝ) ∈ Set.Icc tp (tp + Tobs) :=
    (Set.projIcc tp (tp + Tobs) htAZ t).2
  have hu : ContDiff ℝ ((Nc + (Kmax + 2) : ℕ) : ℕ∞)
      (aRep (Set.projIcc tp (tp + Tobs) htAZ t)) :=
    contDiff_pi.2 fun v => isClassicalRep_contDiff_of_le (w.hrep _ hs v) hJr
  have hup : IsZ2Periodic (aRep (Set.projIcc tp (tp + Tobs) htAZ t)) := fun l x =>
    funext fun v => (w.hrep _ hs v).2.2.1 l x
  exact w.gluedPiece_smooth hJK hJL (fun k => F.weight (pp k)) (w.weight_window) aRep hs hu hup
    (fun v => K v + 2) (fun v => by have := hKmax v; omega)

/-- **The jets of the glued lift of the classical representative are bounded on the window.** -/
theorem ReconWindowAt.gluedRep_jet_le
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Kmax : ℕ} (hKmax : ∀ v, K v ≤ Kmax) (hJK : Kmax + 2 ≤ Klift) (hJL : Kmax + 2 ≤ Llift)
    (hJr : Nc + (Kmax + 2) ≤ r₀) (hr₀K : r₀ + 2 ≤ kc + 1 + (Nc + D)) :
    ∃ CU : ℝ, 0 ≤ CU ∧ ∀ CW : ℝ, 0 ≤ CW → ∀ t ∈ Set.Icc tp (tp + Tobs), (∀ u, ‖W u t‖ ≤ CW) → ∀ v,
      ∀ i ≤ K v + 2, ∀ (w' : DerivativeWord2 i) (x : Vec 2),
        ‖orderedDerivative w' (fun y => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep t y v) x‖ ≤ CU * CW := by
  have htAZ : tp ≤ tp + Tobs := by linarith [w.hTobs]
  obtain ⟨M, hM0, hM⟩ := w.gluedLift_weights_jet_le (J := Kmax + 2) (by omega) (by omega)
  obtain ⟨Ca, hCa0, hCa⟩ := classicalRep_family_iteratedFDeriv_le (h := h) hr₀K
  refine ⟨M * Ca, mul_nonneg hM0 hCa0, fun CW hCW t ht hW v i hi w' x => ?_⟩
  have hiJ : i ≤ Kmax + 2 := hi.trans (by have := hKmax v; omega)
  have hu : ContDiff ℝ ((Nc + (Kmax + 2) : ℕ) : ℕ∞) (aRep t) :=
    contDiff_pi.2 fun v => isClassicalRep_contDiff_of_le (w.hrep t ht v) hJr
  have hc := w.gluedLift_weights_contDiff (fun k => F.weight (pp k)) (w.weight_window) (J := Kmax +
      2) (by omega)
    (by omega) aRep ht hu
  have e : (fun y => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B ρ tp
      (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep t y v) = fun y => obsGlued
              α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep t y v := by
    funext y
    rw [obsGluedClamped_of_mem _ _ _ _ _ _ _ _ _ _ _ htAZ _ _ _ _ _ ht]
  rw [e]
  have hcv : ContDiff ℝ (i : ℕ∞) (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep t y v) :=
    (contDiff_pi.1 (hc.of_le (by exact_mod_cast hiJ)) v)
  refine (AVRegularity.ChartTransport.norm_orderedDerivative_le hcv w' x).trans ?_
  refine (norm_iteratedFDeriv_component_le (hc.of_le (by exact_mod_cast hiJ)) v x).trans ?_
  refine (hM (fun k => F.weight (pp k)) 1 zero_le_one (w.weight_window) aRep t ht
    (fun k hk => w.abs_weight_le k hk t ht) hu (Ca * CW)
    (fun i' hi' y => hCa (fun v => W v t) (aRep t) (w.hrep t ht) hCW hW i' (by omega) y) i hiJ
    x).trans (le_of_eq ?_)
  ring

/-- **The jets of the difference of the glued lifts of an approximant and of the classical
representative** are bounded by the Galerkin errors of `W`. -/
theorem ReconWindowAt.gluedApprox_sub_jet_le
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Kmax : ℕ} (hJK : Kmax + 2 ≤ Klift) (hJL : Kmax + 2 ≤ Llift)
    (hJr : Nc + (Kmax + 2) ≤ r₀) (hr₀K : r₀ + 2 ≤ kc + 1 + (Nc + D)) :
    ∃ CD : ℝ, 0 ≤ CD ∧ ∀ (n : ℕ) (δ : ℝ), 0 ≤ δ → ∀ t ∈ Set.Icc tp (tp + Tobs),
      (∀ u, ‖galerkinProj n (W u t) - W u t‖ ≤ δ) → ∀ j ≤ Kmax + 2, ∀ x,
        ‖iteratedFDeriv ℝ j (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) t y - obsGlued α q Λ m (Φ (m - 1)) hφ
              ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep t y) x‖
          ≤ CD * δ := by
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  obtain ⟨M, hM0, hM⟩ := w.gluedLift_weights_jet_le (J := Kmax + 2) (by omega) (by omega)
  obtain ⟨Cd, hCd0, hCd⟩ := coarseTraj_sub_rep_iteratedFDeriv_le (h := h) hr₀K
  refine ⟨M * Cd, mul_nonneg hM0 hCd0, fun n δ hδ t ht hW j hj x => ?_⟩
  have hu : ContDiff ℝ ((Nc + (Kmax + 2) : ℕ) : ℕ∞) (aRep t) :=
    contDiff_pi.2 fun v => isClassicalRep_contDiff_of_le (w.hrep t ht v) hJr
  have hun : ContDiff ℝ ((Nc + (Kmax + 2) : ℕ) : ℕ∞) (coarseTraj n W t) :=
    (coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top)
  have e : (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp +
      Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) t y - obsGlued α q Λ m (Φ (m - 1)) hφ
              ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep t y) = fun y =>
      obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (fun s y' => coarseTraj n W s y' - aRep s y') t y := by
    funext y
    exact (gluedLift_sub_input_oc hφ hℓ _ _ _ _ _ _ _ _ (coarseTraj n W) aRep (t := t)
      (hun.of_le (by exact_mod_cast Nat.le_add_right Nc (Kmax + 2)))
      (hu.of_le (by exact_mod_cast Nat.le_add_right Nc (Kmax + 2))) y).symm
  rw [e]
  refine (hM (fun k => F.weight (pp k)) 1 zero_le_one (w.weight_window)
    (fun s y' => coarseTraj n W s y' - aRep s y') t ht (fun k hk => w.abs_weight_le k hk t ht)
    (hun.sub hu) (Cd * δ)
    (fun i' hi' y => hCd n W aRep t (w.hrep t ht) hδ hW i' (by omega) y) j hj x).trans
    (le_of_eq ?_)
  ring

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.ChartTransport AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The time integral of the partition term carriers of the approximants**. The
mass-weighted norm of the carrier of the partition term `∑_k ϖ_k' 𝒯_k a_n` at a time of the
window is at most its weighted slice sum (`massNormSq_periodicHk_scal_le`); integrating the
partition bound `partition_term_bound` (taken here as the hypothesis `hPB` on the approximants)
and the Galerkin contraction of the strong energy (`classicalStrongEnergy_coarseTraj_le`) bound
the time integral of the square root by `X` times the strong energy of `W`
(`ReconWindowAt.partition_mass_integral_le`). -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The time integral of the partition term carriers of the approximants.** -/
theorem ReconWindowAt.partition_mass_integral_le
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {r : ℕ} (hrK : r ≤ Klift) (hrL : r ≤ Llift) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r)
    {rs : ℝ} (hrs : 0 ≤ rs) {ord : ℕ} (hord : ord + 1 ≤ kc + 1 + (Nc + D)) {X : ℝ}
    (hPB : ∀ n, ∫⁻ t in Set.Icc tp (tp + Tobs), (∑ j ∈ Finset.range (r + 1), ∑ w' : DerivativeWord2
        j,
          scalInt π (fun x => rs ^ j • orderedDerivative w' (fun x' =>
            ∑ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), deriv (F.weight (pp k)) t •
              pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ
                  m)
                (ocDStar q Λ m ν B / ρ) Nc H (Cc k)
                (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                (coarseTraj n W) t x') x)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal X * classicalStrongEnergy ρ B π (Set.Icc tp (tp
          + Tobs)) ord (coarseTraj n W)) (n : ℕ) :
    ∫⁻ s in Set.Icc tp (tp + Tobs), ENNReal.ofReal (Real.sqrt (massNormSq (E := h) (K := Kc) rs π
        (fun v => (carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k
            => deriv (F.weight (pp k))) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) s x v)).val))) ≤
      ENNReal.ofReal X * strongEnergyUpTo ρ B π tp (tp + Tobs) ord W
          := by
  have hπ := w.hcs.mass_pos
  refine le_trans ?_ ((hPB n).trans (mul_le_mul_right
    (classicalStrongEnergy_coarseTraj_le hord _ B π tp (tp + Tobs) n W) _))
  refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  obtain ⟨hs, hp⟩ := w.gluedPiece_smooth hrK hrL (fun k => deriv (F.weight (pp k)))
      (w.deriv_weight_window)
    (coarseTraj n W) ht ((coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top))
    (coarseTraj_periodic n W t) Kc hKr
  have hq := w.gluedLift_weights_contDiff (fun k => deriv (F.weight (pp k))) (w.deriv_weight_window)
      (J := r) (by omega)
    (by omega) (coarseTraj n W) ht ((coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top))
  have e : (fun v => (carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun
      k => deriv (F.weight (pp k))) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) t x v)).val) =
      fun v => (periodicHk (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k =>
          deriv (F.weight (pp k))) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) t x v) (hs v) (hp v)).val :=
    funext fun v => by rw [carrierOf_eq (Kc v) (hs v) (hp v)]
  rw [e]
  have hm := massNormSq_periodicHk_scal_le Kc hKr hrs π hπ _ hq hs hp
  have h0 := massNormSq_nonneg (E := h) (K := Kc) rs π hπ
    (fun v => (periodicHk (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k =>
        deriv (F.weight (pp k))) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) t x v) (hs v) (hp v)).val)
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg h0 (by norm_num)]
  exact ENNReal.rpow_le_rpow hm (by norm_num)

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Cell `L²` facts for the packaging of the reconstruction**. A bounded
a.e. strongly measurable field is square integrable on the cell with norm at most the bound
(`memLp_cell_and_le_of_bound`); the value jet of a torus Sobolev element is square integrable on
the cell with norm at most its norm (`torusHk_value_memLp_le`), also componentwise
(`torusHk_value_component_memLp_le`); and a smooth periodic field minus the value jet of an
element is controlled by the norm of the difference of the carriers
    (`periodicHk_sub_value_memLp_le`,
`periodicHk_sub_value_component_memLp_le`). -/

section
/-- The cell measure is finite. -/
theorem isFiniteMeasure_cell : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simp only [Measure.restrict_apply_univ, AVRegularity.EntryWeakProofs.weak_unitCube_volume]
      exact ENNReal.one_lt_top⟩

section Bound

variable {F : Type*} [NormedAddCommGroup F]

/-- **A bounded a.e. strongly measurable field is square integrable on the cell**, with norm at
most the bound. -/
theorem memLp_cell_and_le_of_bound {f : Vec 2 → F}
    (hf : AEStronglyMeasurable f (volume.restrict AVenhance.unitCube)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖f x‖ ≤ C) :
    MemLp f 2 (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm f 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C := by
  have := isFiniteMeasure_cell
  exact ⟨MemLp.of_bound hf C (Filter.Eventually.of_forall hb), cellL2_le_of_bound hf hC hb⟩

end Bound

section Value

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- **The value jet of a torus Sobolev element is square integrable on the cell**, with norm at
most the norm of the element. -/
theorem torusHk_value_memLp_le {K : ℕ} (U : TorusHk K E) :
    MemLp (U.toFunction.jet (valueIndex2 K)) 2 (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (U.toFunction.jet (valueIndex2 K)) 2
        (volume.restrict AVenhance.unitCube)).toReal ≤ ‖U‖ := by
  have hae := AVRegularity.KernelEnergy.torusHk_toFunction_jet_ae U (valueIndex2 K)
  refine ⟨(Lp.memLp (U.val (valueIndex2 K))).ae_eq hae.symm, ?_⟩
  rw [eLpNorm_congr_ae hae, ← Lp.norm_def]
  exact PiLp.norm_apply_le U.val (valueIndex2 K)

/-- **A smooth periodic field minus the value jet of an element** is square integrable on the
cell, with norm at most the norm of the difference of the carriers. -/
theorem periodicHk_sub_value_memLp_le {K : ℕ} {f : Vec 2 → E} (hf : ContDiff ℝ (K : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) (V : TorusHk K E) :
    MemLp (fun x => f x - V.toFunction.jet (valueIndex2 K) x) 2
        (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (fun x => f x - V.toFunction.jet (valueIndex2 K) x) 2
        (volume.restrict AVenhance.unitCube)).toReal ≤ ‖periodicHk K f hf hp - V‖ := by
  have hae : (periodicHk K f hf hp - V).toFunction.jet (valueIndex2 K)
      =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => f x - V.toFunction.jet (valueIndex2 K) x := by
    filter_upwards [AVRegularity.KernelEnergy.torusHk_toFunction_jet_ae
        (periodicHk K f hf hp - V) (valueIndex2 K),
      AVRegularity.KernelEnergy.torusHk_toFunction_jet_ae V (valueIndex2 K),
      AVRegularity.KernelEnergy.torusHk_toFunction_jet_ae (periodicHk K f hf hp) (valueIndex2 K),
      periodicHk_value_ae K f hf hp,
      Lp.coeFn_sub ((periodicHk K f hf hp).val (valueIndex2 K)) (V.val (valueIndex2 K))]
      with x h1 h2 h3 h4 h5
    rw [h1, h2]
    have hc : (periodicHk K f hf hp - V).val (valueIndex2 K) =
        (periodicHk K f hf hp).val (valueIndex2 K) - V.val (valueIndex2 K) := rfl
    rw [hc, h5, Pi.sub_apply, ← h3, h4]
  obtain ⟨hm, hl⟩ := torusHk_value_memLp_le (periodicHk K f hf hp - V)
  exact ⟨hm.ae_eq hae, (le_of_eq (by rw [eLpNorm_congr_ae hae])).trans hl⟩

end Value

section Component

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [CompleteSpace F] [FiniteDimensional ℝ F]

omit [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [FiniteDimensional ℝ F] in
/-- A component of a square integrable field with values in `F²` is square integrable, with norm
at most the norm of the field. -/
theorem memLp_component_le {g : Vec 2 → PiLp 2 (fun _ : Fin 2 => F)}
    (hg : MemLp g 2 (volume.restrict AVenhance.unitCube)) (k : Fin 2) :
    MemLp (fun x => g x k) 2 (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (fun x => g x k) 2 (volume.restrict AVenhance.unitCube)).toReal ≤
        (eLpNorm g 2 (volume.restrict AVenhance.unitCube)).toReal := by
  have hle : ∀ x, ‖g x k‖ ≤ ‖g x‖ := fun x => PiLp.norm_apply_le (g x) k
  have hm : MemLp (fun x => g x k) 2 (volume.restrict AVenhance.unitCube) :=
    hg.of_le (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => F) k).continuous.comp_aestronglyMeasurable
      hg.aestronglyMeasurable)) (Filter.Eventually.of_forall hle)
  exact ⟨hm, ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono hm.aestronglyMeasurable hle)⟩

/-- **The components of the value jet of an element are square integrable on the cell.** -/
theorem torusHk_value_component_memLp_le {K : ℕ} (U : TorusHk K (PiLp 2 (fun _ : Fin 2 => F)))
    (k : Fin 2) :
    MemLp (fun x => (U.toFunction.jet (valueIndex2 K) x) k) 2
        (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (fun x => (U.toFunction.jet (valueIndex2 K) x) k) 2
        (volume.restrict AVenhance.unitCube)).toReal ≤ ‖U‖ := by
  obtain ⟨hm, hl⟩ := torusHk_value_memLp_le U
  obtain ⟨hk, hkl⟩ := memLp_component_le hm k
  exact ⟨hk, hkl.trans hl⟩

/-- **The components of a smooth periodic field minus the value jet of an element.** -/
theorem periodicHk_sub_value_component_memLp_le {K : ℕ} {f : Vec 2 → PiLp 2 (fun _ : Fin 2 => F)}
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f)
    (V : TorusHk K (PiLp 2 (fun _ : Fin 2 => F))) (k : Fin 2) :
    MemLp (fun x => (f x - V.toFunction.jet (valueIndex2 K) x) k) 2
        (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (fun x => (f x - V.toFunction.jet (valueIndex2 K) x) k) 2
        (volume.restrict AVenhance.unitCube)).toReal ≤ ‖periodicHk K f hf hp - V‖ := by
  obtain ⟨hm, hl⟩ := periodicHk_sub_value_memLp_le hf hp V
  obtain ⟨hk, hkl⟩ := memLp_component_le hm k
  exact ⟨hk, hkl.trans hl⟩

end Component
end

/-! **Edge fluxes of smooth fields**. The edge flux `edgeFluxOf K A s U` of a field
whose jets of the admissible orders are bounded by `CJ`, with coefficients bounded by `CA`, is
bounded pointwise by `E₀ CA CJ` (`edgeFluxOf_norm_le`); it is linear in the field
(`edgeFluxOf_sub`) and a.e. strongly measurable on the cell when the coefficients are
(`edgeFluxOf_aestronglyMeasurable`); hence its components are square integrable on the cell with
norm at most `E₀ CA CJ` (`edgeFluxOf_component_memLp_le`). -/

section
/-- The combinatorial constant of the edge fluxes. -/
def edgeFluxConst {ι : Type*} [Fintype ι] (K : ι → ℕ) (D : ℕ) : ℝ :=
  ∑ v, ∑ i' : ι, ((admissibleOrders K D v i').card : ℝ) * 2 ^ D

theorem edgeFluxConst_nonneg {ι : Type*} [Fintype ι] (K : ι → ℕ) (D : ℕ) : 0 ≤ edgeFluxConst K D :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
/-- **Pointwise bound of the edge flux.** -/
theorem edgeFluxOf_norm_le (K : ι → ℕ) {D : ℕ}
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i)))
    (s : ℝ) (U : Vec 2 → ∀ i, h i) (v : ι) (x : Vec 2) {CA CJ : ℝ} (hCA : 0 ≤ CA)
    (hCJ : 0 ≤ CJ) (hA : ∀ i' d, ‖A v i' d s x‖ ≤ CA)
    (hJ : ∀ i' (d : admissibleOrders K D v i') (word : DerivativeWord2 (d.1 - 1)),
      ‖orderedDerivative word (fun y => U y i') x‖ ≤ CJ) :
    ‖edgeFluxOf K A s U v x‖ ≤ edgeFluxConst K D * CA * CJ := by
  have hterm : ∀ i' (d : admissibleOrders K D v i'), ‖A v i' d s x
      (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word (fun y => U y i') x)‖ ≤ CA * (2 ^ D * CJ) := fun i' d => by
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hA i' d) ?_ (norm_nonneg _) hCA)
    refine (AVRegularity.Weighted.finitePiLp_norm_le_sum _).trans ?_
    refine (Finset.sum_le_sum fun word _ => hJ i' d word).trans ?_
    rw [Finset.sum_const, AVRegularity.ChartTransport.card_derivativeWord2, nsmul_eq_mul]
    push_cast
    have hd : d.1 - 1 ≤ D := by have := (Finset.mem_filter.1 d.2).1; simp at this; omega
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hd) hCJ
  unfold edgeFluxOf
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i' _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun d _ => hterm i' d)).trans ?_
  have hv : ∑ i' : ι, ((admissibleOrders K D v i').card : ℝ) * 2 ^ D ≤ edgeFluxConst K D :=
    Finset.single_le_sum (f := fun v => ∑ i' : ι, ((admissibleOrders K D v i').card : ℝ) * 2 ^ D)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ v)
  calc ∑ i' : ι, ∑ _d : admissibleOrders K D v i', CA * (2 ^ D * CJ)
      = (∑ i' : ι, ((admissibleOrders K D v i').card : ℝ) * 2 ^ D) * CA * CJ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun i' _ => by ring
    _ ≤ edgeFluxConst K D * CA * CJ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv hCA) hCJ

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
/-- **The edge flux is linear in the field.** -/
theorem edgeFluxOf_sub (K : ι → ℕ) {D : ℕ}
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i)))
    (s : ℝ) (U V : Vec 2 → ∀ i, h i) (hU : ∀ i', ContDiff ℝ ((K i' + 1 : ℕ) : ℕ∞) (fun y => U y i'))
    (hV : ∀ i', ContDiff ℝ ((K i' + 1 : ℕ) : ℕ∞) (fun y => V y i')) (v : ι) (x : Vec 2) :
    edgeFluxOf K A s (fun y => U y - V y) v x = edgeFluxOf K A s U v x - edgeFluxOf K A s V v x :=
        by
  unfold edgeFluxOf
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← map_sub]
  congr 1
  rw [← WithLp.toLp_sub]
  congr 1
  funext word
  have hd := admissibleOrders_sub_one_le d
  have e := orderedDerivative_sub word ((hU i').of_le (by exact_mod_cast hd))
    ((hV i').of_le (by exact_mod_cast hd))
  exact congrFun e x

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **The edge flux of a smooth field is a.e. strongly measurable on the cell** when the
coefficients are. -/
theorem edgeFluxOf_aestronglyMeasurable (K : ι → ℕ) {D : ℕ}
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i)))
    (s : ℝ) (U : Vec 2 → ∀ i, h i) (hU : ∀ i', ContDiff ℝ ((K i' + 1 : ℕ) : ℕ∞) (fun y => U y i'))
    (v : ι)
    (hA : ∀ i' d, AEStronglyMeasurable (A v i' d s) (volume.restrict AVenhance.unitCube)) :
    AEStronglyMeasurable (fun x => edgeFluxOf K A s U v x)
      (volume.restrict AVenhance.unitCube) := by
  unfold edgeFluxOf
  refine Finset.aestronglyMeasurable_fun_sum _ fun i' _ =>
    Finset.aestronglyMeasurable_fun_sum _ fun d _ => ?_
  have hd := admissibleOrders_sub_one_le d
  have hc : Continuous (fun x => (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      orderedDerivative word (fun y => U y i') x : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) =>
        h i'))) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun word =>
      AVRegularity.ChartTransport.continuous_orderedDerivative word
        ((hU i').of_le (by exact_mod_cast hd)))
  exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    ((hA i' d).prodMk hc.aestronglyMeasurable)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **The components of the edge flux of a smooth field are square integrable on the cell.** -/
theorem edgeFluxOf_component_memLp_le (K : ι → ℕ) {D : ℕ}
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i)))
    (s : ℝ) (U : Vec 2 → ∀ i, h i) (hU : ∀ i', ContDiff ℝ ((K i' + 1 : ℕ) : ℕ∞) (fun y => U y i'))
    (v : ι) (hAm : ∀ i' d, AEStronglyMeasurable (A v i' d s) (volume.restrict AVenhance.unitCube))
    {CA CJ : ℝ} (hCA : 0 ≤ CA) (hCJ : 0 ≤ CJ) (hA : ∀ i' d x, ‖A v i' d s x‖ ≤ CA)
    (hJ : ∀ i' (d : admissibleOrders K D v i') (word : DerivativeWord2 (d.1 - 1)) x,
      ‖orderedDerivative word (fun y => U y i') x‖ ≤ CJ) (k : Fin 2) :
    MemLp (fun x => edgeFluxOf K A s U v x k) 2 (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (fun x => edgeFluxOf K A s U v x k) 2
        (volume.restrict AVenhance.unitCube)).toReal ≤ edgeFluxConst K D * CA * CJ := by
  have hm := edgeFluxOf_aestronglyMeasurable K A s U hU v hAm
  refine memLp_cell_and_le_of_bound ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h v)
    k).continuous.comp_aestronglyMeasurable hm)
    (mul_nonneg (mul_nonneg (edgeFluxConst_nonneg K D) hCA) hCJ) fun x => ?_
  exact (PiLp.norm_apply_le _ k).trans (edgeFluxOf_norm_le K A s U v x hCA hCJ
    (fun i' d => hA i' d x) fun i' d word => hJ i' d word x)
end

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The physical lift is a coupled weak solution with the limit residual**. The
torus Sobolev trajectory of the clamped glued lift of `aRep` solves the coupled equation of the
window with the residual `(R, q)`, given the limits of the residuals of the approximants with
distance bounds whose integrals tend to zero (`ReconWindowAt.physical_weak_solution`, from
`isCoupledWeakSolutionTorus_of_approximants` and the approximant identity
`ReconWindowAt.approx_identity`). -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The physical lift solves the coupled equation with the limit residual.** -/
theorem ReconWindowAt.physical_weak_solution
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Kmax : ℕ} (hKmax : ∀ v, K v ≤ Kmax) (hJK : Kmax + 2 ≤ Klift) (hJL : Kmax + 2 ≤ Llift)
    (hJr : Nc + (Kmax + 2) ≤ r₀) (hr₀K : r₀ + 2 ≤ kc + 1 + (Nc + D)) (hDL : D ≤ Llift + 2)
    {sXc sZc Acl sXl sZl : ℕ} (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc ≤ Klift + D + 2) (hZ : sZc ≤ Llift + 2) (hXl : 1 ≤ sXl) (hZl : 1 ≤ sZl)
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n sXc sZc Acl sXl sZl (Vc n) (Vn n))
    {Vb : ℝ}
    (hbm : ∀ s ∈ Set.Ioc tp (tp + Tobs), ∀ k,
      AEStronglyMeasurable (fun x => streamVel (Φ m) s x k) (volume.restrict AVenhance.unitCube))
    (hVb : ∀ s ∈ Set.Ioc tp (tp + Tobs), ∀ x k, |streamVel (Φ m) s x k| ≤ Vb)
    {CA : ℝ} (hCA : 0 ≤ CA)
    (hAb : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v u d x, ‖(edgeCoefficient F ν (ocEpsilon q Λ m)
        (ocEpsilon q Λ (m - 1)) actual K) v u d s x‖ ≤ CA)
    (hAm : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v u d,
      AEStronglyMeasurable ((edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
          v u d s) (volume.restrict AVenhance.unitCube))
    {CW : ℝ} (hCW : 0 ≤ CW) (hWB : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ u, ‖W u s‖ ≤ CW)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hWδ : ∀ n, ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ u, ‖galerkinProj n (W u s) - W u s‖ ≤ δ n)
    (R : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
    (Q : ∀ v, ℝ → TorusHk (K v) (h v)) (cR cq : ℕ → ℝ → ℝ)
    (hcR : ∀ n, IntegrableOn (cR n) (Set.Icc tp (tp + Tobs)))
    (hcR0 : Tendsto (fun n => ∫ s in Set.Icc tp (tp + Tobs), cR n s) atTop (𝓝 0))
    (hcRp : ∀ n s, 0 ≤ cR n s)
    (hcq : ∀ n, IntegrableOn (cq n) (Set.Icc tp (tp + Tobs)))
    (hcq0 : Tendsto (fun n => ∫ s in Set.Icc tp (tp + Tobs), cq n s) atTop (𝓝 0))
    (hcqp : ∀ n s, 0 ≤ cq n s)
    (hFs : ∀ n, ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v, ContDiff ℝ (K v : ℕ∞) (fun x => approxFlux α q Λ
        m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v s x) ∧
      IsZ2Periodic (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ
          tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v s x))
    (hQs : ∀ n, ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v, ContDiff ℝ (K v : ℕ∞) (fun x => approxForce α q Λ
        m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v s x) ∧
      IsZ2Periodic (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v s x))
    (hRc : ∀ n, ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v,
      ‖carrierOf (K v) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v s x) - R v s‖ ≤ cR n s)
    (hqc : ∀ n, ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v,
      ‖carrierOf (K v) (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v s x) - Q v s‖ ≤ cq n s)
    (CRq : ℝ → ℝ) (hCRq : IntegrableOn CRq (Set.Icc tp (tp + Tobs)))
    (hRq : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v, ‖R v s‖ ≤ CRq s ∧ ‖Q v s‖ ≤ CRq s) :
    IsCoupledWeakSolutionTorus ν tp (tp + Tobs) (streamVel (Φ m)) D K (edgeCoefficient F ν
        (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (fun v => periodicHk (K v) (fun x => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep tp x v)
        (((w.gluedRep_smooth hKmax hJK hJL hJr tp).1 v).of_le
          (by exact_mod_cast Nat.le_add_right (K v) 2))
        ((w.gluedRep_smooth hKmax hJK hJL hJr tp).2 v)) R Q
      (fun v t => periodicHk (K v) (fun x => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep t x v)
        (((w.gluedRep_smooth hKmax hJK hJL hJr t).1 v).of_le
          (by exact_mod_cast Nat.le_add_right (K v) 2))
        ((w.gluedRep_smooth hKmax hJK hJL hJr t).2 v))
      (fun v t => periodicHk (K v + 1) (fun x => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B
          ρ tp (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep t x v)
        (((w.gluedRep_smooth hKmax hJK hJL hJr t).1 v).of_le (by exact_mod_cast Nat.le_succ (K v +
            1)))
        ((w.gluedRep_smooth hKmax hJK hJL hJr t).2 v)) := by
  have htAZ : tp ≤ tp + Tobs := by linarith [w.hTobs]
  have hIoc : Set.Ioc tp (tp + Tobs) ⊆ Set.Icc tp (tp + Tobs) := Set.Ioc_subset_Icc_self
  obtain ⟨CU₀, hCU₀, hUb⟩ := w.gluedRep_jet_le hKmax hJK hJL hJr hr₀K
  obtain ⟨CD, hCD, hUd⟩ := w.gluedApprox_sub_jet_le hJK hJL hJr hr₀K
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ, E₀ = edgeFluxConst K D := ⟨_, rfl⟩
  have hE₀0 : 0 ≤ E₀ := hE₀ ▸ edgeFluxConst_nonneg K D
  have hsm := fun t => w.gluedRep_smooth hKmax hJK hJL hJr t
  -- the glued lifts at the times of the window are smooth
  have hcU : ∀ t ∈ Set.Icc tp (tp + Tobs), ContDiff ℝ ((Kmax + 2 : ℕ) : ℕ∞) (fun x => obsGlued α q Λ
      m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep t x) :=
    fun t ht => w.gluedLift_weights_contDiff (fun k => F.weight (pp k)) (w.weight_window)
      (J := Kmax + 2) (by omega) (by omega) aRep ht
      (contDiff_pi.2 fun v => isClassicalRep_contDiff_of_le (w.hrep t ht v) hJr)
  have hcN : ∀ n, ∀ t ∈ Set.Icc tp (tp + Tobs), ContDiff ℝ ((Kmax + 2 : ℕ) : ℕ∞)
      (fun x => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) t x) :=
    fun n t ht => w.gluedLift_weights_contDiff (fun k => F.weight (pp k)) (w.weight_window)
      (J := Kmax + 2) (by omega) (by omega) (coarseTraj n W) ht
      ((coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top))
  have hUeq : ∀ t ∈ Set.Icc tp (tp + Tobs), (fun x => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B
      ρ tp (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep t x) = fun x => obsGlued α
              q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep t x :=
    fun t ht => funext fun x => obsGluedClamped_of_mem _ _ _ _ _ _ _ _ _ _ _ htAZ _ _ _ _ _ ht x
  -- the differences of the approximants
  have hdiff : ∀ n, ∀ t ∈ Set.Icc tp (tp + Tobs), ∀ j ≤ Kmax + 2, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) t y - obsGlued α q Λ m (Φ (m - 1)) hφ
              ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep t y) x‖ ≤
        CD * δ n :=
    fun n t ht => hUd n (δ n) (hδ0 n) t ht (hWδ n t ht)
  -- the differences of the lifts in `L²`
  have hD0 : ∀ n, ∀ t ∈ Set.Icc tp (tp + Tobs), ∀ v,
      MemLp (fun x => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp +
          Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) t x v - obsGluedClamped α q Λ m (Φ (m
              - 1)) hφ ν B ρ tp (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep t x v) 2
        (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (fun x => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp
          (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) t x v - obsGluedClamped α q Λ m (Φ (m
              - 1)) hφ ν B ρ tp (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep t x v) 2
        (volume.restrict AVenhance.unitCube)).toReal ≤ CD * δ n := fun n t ht v => by
    have e : (fun x => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp
        + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) t x v - obsGluedClamped α q Λ m (Φ (m
              - 1)) hφ ν B ρ tp (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep t x v) = fun x =>
        (obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) t x - obsGlued α q Λ m (Φ (m - 1)) hφ
              ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep t x) v := funext fun x => by
      rw [obsGluedClamped_of_mem _ _ _ _ _ _ _ _ _ _ _ htAZ _ _ _ _ _ ht x]
      rfl
    rw [e]
    refine memLp_cell_and_le_of_bound ((continuous_apply v).comp ((hcN n t ht).continuous.sub
      (hcU t ht).continuous)).aestronglyMeasurable (mul_nonneg hCD (hδ0 n)) fun x => ?_
    refine (norm_le_pi_norm _ v).trans ?_
    have h0 := hdiff n t ht 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero] at h0
    exact h0
  -- the constant `C`, the rate `c`
  obtain ⟨CU, hCUdef⟩ : ∃ CU : ℝ, CU = CU₀ * CW := ⟨_, rfl⟩
  have hCU : 0 ≤ CU := hCUdef ▸ mul_nonneg hCU₀ hCW
  have hCE : 0 ≤ E₀ * CA * CU := mul_nonneg (mul_nonneg hE₀0 hCA) hCU
  have hcn : ∀ n, 0 ≤ CD * δ n := fun n => mul_nonneg hCD (hδ0 n)
  refine isCoupledWeakSolutionTorus_of_approximants htAZ (streamVel (Φ m)) Vb hbm hVb K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
    (fun t x => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp
        + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep t x) (fun t v => (hsm t).1
              v) (fun t v => (hsm t).2 v) hCU
    (fun t ht v i hi w' x => hCUdef ▸ hUb CW hCW t ht (hWB t ht) v i hi w' x) R Q
    (fun s => CU + E₀ * CA * CU + |CRq s|)
    (((integrableOn_const (C := CU + E₀ * CA * CU) (by simp)).add hCRq.abs).mono_set hIoc)
    (fun s _ => le_add_of_le_of_nonneg (le_add_of_nonneg_right hCE) (abs_nonneg _))
    (fun s hs v k => ?_) (fun s hs v k => ?_) (fun s hs v => ?_)
    (fun n s x => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp +
        Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s x)
    (fun n v s x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp +
        Tobs)
          (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v s x) (fun n v s x => approxForce
              α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v s x)
    (fun n t ht v => ?_) (fun t ht v => ?_)
    (fun n s => CD * δ n + E₀ * CA * (CD * δ n) + cR n s + cq n s)
    (fun n => ((((integrableOn_const (C := CD * δ n) (by simp)).add
      (integrableOn_const (C := E₀ * CA * (CD * δ n)) (by simp))).add (hcR n)).add
        (hcq n)).mono_set hIoc) ?_
    (fun n s hs v k => ?_) (fun n s hs v k => ?_) (fun n s hs v k => ?_) (fun n s hs v => ?_)
    (fun n t ht v φ hφ' hφp => w.approx_identity hDL n sXc sZc Acl sXl sZl hAcl hXc hZc hX hZ
      hXl hZl (Vc n) (Vn n) (hch n) t ht v φ hφ' hφp)
  · -- the edge flux of the lift
    have hs' := hIoc hs
    obtain ⟨hm, hl⟩ := edgeFluxOf_component_memLp_le K (edgeCoefficient F ν (ocEpsilon q Λ m)
        (ocEpsilon q Λ (m - 1)) actual K) s (fun x => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B
        ρ tp (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep s x)
      (fun i' => ((hsm s).1 i').of_le (by exact_mod_cast Nat.le_succ (K i' + 1))) v
      (hAm s hs' v) hCA hCU (fun i' d x => hAb s hs' v i' d x)
      (fun i' d word x => hCUdef ▸ hUb CW hCW s hs' (hWB s hs') i' (d.1 - 1)
        (by have := admissibleOrders_sub_one_le d; omega) word x) k
    refine ⟨hm, hl.trans ?_⟩
    rw [← hE₀]
    exact le_add_of_le_of_nonneg (le_add_of_nonneg_left hCU) (abs_nonneg _)
  · -- the residual flux
    obtain ⟨hm, hl⟩ := torusHk_value_component_memLp_le (R v s) k
    exact ⟨hm, hl.trans (((hRq s (hIoc hs) v).1.trans (le_abs_self _)).trans
      (le_add_of_nonneg_left (add_nonneg hCU hCE)))⟩
  · -- the residual force
    obtain ⟨hm, hl⟩ := torusHk_value_memLp_le (Q v s)
    exact ⟨hm, hl.trans (((hRq s (hIoc hs) v).2.trans (le_abs_self _)).trans
      (le_add_of_nonneg_left (add_nonneg hCU hCE)))⟩
  · -- square integrability of the differences of the lifts
    exact (hD0 n t ht v).1
  · exact squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => (hD0 n t ht v).2)
      (by simpa using hδ.const_mul CD)
  · -- the integrals of the rates tend to zero
    have hI : ∀ n, ∫ s in Set.Ioc tp (tp + Tobs), (CD * δ n + E₀ * CA * (CD * δ n) + cR n s + cq n
        s) =
        volume.real (Set.Ioc tp (tp + Tobs)) * (CD * δ n + E₀ * CA * (CD * δ n)) +
          (∫ s in Set.Icc tp (tp + Tobs), cR n s) + ∫ s in Set.Icc tp (tp + Tobs), cq n s := fun n
              => by
      rw [integral_add (f := fun s => CD * δ n + E₀ * CA * (CD * δ n) + cR n s) (g := cq n)
          (((integrableOn_const (C := CD * δ n + E₀ * CA * (CD * δ n))
          (by simp)).add (hcR n)).mono_set hIoc) ((hcq n).mono_set hIoc),
        integral_add (f := fun _ => CD * δ n + E₀ * CA * (CD * δ n)) (g := cR n)
          (integrableOn_const (by simp)) ((hcR n).mono_set hIoc), setIntegral_const,
        smul_eq_mul, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
    simp only [hI]
    have h1 := ((((hδ.const_mul CD).add ((hδ.const_mul CD).const_mul (E₀ * CA))).const_mul
      (volume.real (Set.Ioc tp (tp + Tobs)))).add hcR0).add hcq0
    simpa using h1
  · -- the derivatives of the differences
    have hs' := hIoc hs
    have eU : (fun y => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs)
          (by linarith [w.hTobs]) (fun k => F.weight (pp k)) Nc H Cc aRep s y v) = fun y => obsGlued
              α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep s y v :=
      funext fun y => by rw [obsGluedClamped_of_mem _ _ _ _ _ _ _ _ _ _ _ htAZ _ _ _ _ _ hs' y]
    rw [eU]
    have hfd : ∀ x, DifferentiableAt ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s y v) x := fun x =>
      ((contDiff_pi.1 (hcN n s hs') v).differentiable (by simp)) x
    have hgd : ∀ x, DifferentiableAt ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep s y v) x := fun x =>
      ((contDiff_pi.1 (hcU s hs') v).differentiable (by simp)) x
    have hd : (fun x => fderiv ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s y v) x (basisVec k) -
        fderiv ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp
            (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep s y v) x (basisVec k)) = fun x =>
        fderiv ℝ (fun y => (obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp
            (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s y - obsGlued α q Λ m (Φ (m - 1)) hφ
              ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep s y) v) x (basisVec k) := funext fun x => by
      rw [show (fun y => (obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp
          (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s y - obsGlued α q Λ m (Φ (m - 1)) hφ
              ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep s y) v) = fun y => obsGlued α q Λ m (Φ (m - 1)) hφ
              ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s y v - obsGlued α q Λ m (Φ (m - 1))
              hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep s y v from rfl,
        fderiv_fun_sub (hfd x) (hgd x)]
      rfl
    rw [hd]
    have hsub : ContDiff ℝ ((Kmax + 2 : ℕ) : ℕ∞) (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B
        ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s y - obsGlued α q Λ m (Φ (m - 1)) hφ
              ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep s y) :=
      (hcN n s hs').sub (hcU s hs')
    have hsubv : ContDiff ℝ ((Kmax + 2 : ℕ) : ℕ∞) (fun y => (obsGlued α q Λ m (Φ (m - 1)) hφ ν B
        ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s y - obsGlued α q Λ m (Φ (m - 1)) hφ
              ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep s y) v) :=
      contDiff_pi.1 hsub v
    obtain ⟨hm, hl⟩ := memLp_cell_and_le_of_bound
      (((hsubv.continuous_fderiv (by simp)).clm_apply
        (continuous_const (y := (basisVec k : Vec 2)))).aestronglyMeasurable)
      (hcn n) fun x => by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [norm_basisVec, mul_one, ← norm_iteratedFDeriv_one]
        exact (norm_iteratedFDeriv_component_le (hsub.of_le (by exact_mod_cast
          (by omega : 1 ≤ Kmax + 2))) v x).trans (hdiff n s hs' 1 (by omega) x)
    exact ⟨hm, hl.trans (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
      (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hE₀0 hCA) (hcn n))) (hcRp n s)) (hcqp n s))⟩
  · -- the edge fluxes of the differences
    have hs' := hIoc hs
    beta_reduce
    rw [hUeq s hs']
    have hsub : ContDiff ℝ ((Kmax + 2 : ℕ) : ℕ∞) (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B
        ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s y - obsGlued α q Λ m (Φ (m - 1)) hφ
              ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep s y) :=
      (hcN n s hs').sub (hcU s hs')
    have hcomp : ∀ (f : Vec 2 → ∀ i, h i), ContDiff ℝ ((Kmax + 2 : ℕ) : ℕ∞) f →
        ∀ i', ContDiff ℝ ((K i' + 1 : ℕ) : ℕ∞) (fun y => f y i') := fun f hf i' =>
      (contDiff_pi.1 hf i').of_le (by exact_mod_cast (by have := hKmax i'; omega :
        K i' + 1 ≤ Kmax + 2))
    have e : (fun x => (edgeFluxOf K (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1))
        actual K) s (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s y) v x -
        edgeFluxOf K (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) s (fun
            y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp +
            Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep s y) v x) k) = fun x =>
        edgeFluxOf K (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) s (fun
            y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp +
            Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s y - obsGlued α q Λ m (Φ (m - 1)) hφ
              ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep s y) v x k := funext fun x => by
      rw [edgeFluxOf_sub K (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
          s _ _ (hcomp _ (hcN n s hs')) (hcomp _ (hcU s hs')) v x]
    rw [e]
    obtain ⟨hm, hl⟩ := edgeFluxOf_component_memLp_le K (edgeCoefficient F ν (ocEpsilon q Λ m)
        (ocEpsilon q Λ (m - 1)) actual K) s (fun y => obsGlued α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc (coarseTraj n W) s y - obsGlued α q Λ m (Φ (m - 1)) hφ
              ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) Nc H Cc aRep s y)
      (hcomp _ hsub) v (hAm s hs' v) hCA (hcn n) (fun i' d x => hAb s hs' v i' d x)
      (fun i' d word x => by
        have hd := admissibleOrders_sub_one_le d
        have hdK : d.1 - 1 ≤ Kmax + 2 := by have := hKmax i'; omega
        refine (AVRegularity.ChartTransport.norm_orderedDerivative_le
          ((contDiff_pi.1 hsub i').of_le (by exact_mod_cast hdK)) word x).trans ?_
        exact (norm_iteratedFDeriv_component_le (hsub.of_le (by exact_mod_cast hdK)) i'
          x).trans (hdiff n s hs' (d.1 - 1) hdK x)) k
    refine ⟨hm, hl.trans ?_⟩
    rw [← hE₀]
    exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg (le_add_of_nonneg_left (hcn n))
      (hcRp n s)) (hcqp n s)
  · -- the residual fluxes
    have hs' := hIoc hs
    obtain ⟨hm, hl⟩ := periodicHk_sub_value_component_memLp_le (hFs n s hs' v).1
      (hFs n s hs' v).2 (R v s) k
    rw [← carrierOf_eq (K v) (hFs n s hs' v).1 (hFs n s hs' v).2] at hl
    exact ⟨hm, (hl.trans (hRc n s hs' v)).trans (le_add_of_le_of_nonneg
      (le_add_of_nonneg_left (add_nonneg (hcn n) (mul_nonneg (mul_nonneg hE₀0 hCA) (hcn n))))
      (hcqp n s))⟩
  · -- the residual forces
    have hs' := hIoc hs
    obtain ⟨hm, hl⟩ := periodicHk_sub_value_memLp_le (hQs n s hs' v).1 (hQs n s hs' v).2 (Q v s)
    rw [← carrierOf_eq (K v) (hQs n s hs' v).1 (hQs n s hs' v).2] at hl
    exact ⟨hm, (hl.trans (hqc n s hs' v)).trans (le_add_of_nonneg_left (add_nonneg
      (add_nonneg (hcn n) (mul_nonneg (mul_nonneg hE₀0 hCA) (hcn n))) (hcRp n s)))⟩

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.ChartTransport AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The time integral of the residual force of the reconstruction**. The
residual force `qq` is the limit of the forcing residual carriers of the approximants, which split
into the glued residual force (bounded at every time by the separated densities, `β`), the glued
lift of the commutator remainder (vanishing in the limit) and the partition term (with integrals
bounded by `X` times the strong energy of `W`); hence `∫ √mass(qq) ≤ ∫ β + X E_b`
(`ReconWindowAt.force_bill`, by `integral_sqrt_massNormSq_le_of_split`). -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The time integral of the residual force of the reconstruction.** -/
theorem ReconWindowAt.force_bill
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (hSb : 0 ≤ Sb) {Acl r m' kres Nχ : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (hk : Acl + 2 + r + Nc + 1 ≤ kres) (hNχ : m' + 1 ≤ Nχ) (hNχ' : kres + 1 ≤ Nχ)
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ Nc →
      ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ Acl + 2 + r →
        schurEnergyJet π (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp /
            ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2))
          Llift j (Cc k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ρ / ocEpsilon q Λ (m - 1)) ^ (n - m'' + j)))
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (hkres : kres ≤ kc) (hmr : m' + 1 ≤ r₀)
    (hNco : Nc + r + 1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r)
    (qq : ℝ → ∀ v, TorusHk (Kc v) (h v))
    (hqlim : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v, Tendsto (fun n => carrierOf (Kc v) (fun x =>
        approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v s x))
      atTop (𝓝 (qq s v)))
    (hqm : ∀ v, AEStronglyMeasurable (fun s => qq s v) (volume.restrict (Set.Icc tp (tp + Tobs))))
    (hE0 : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ ε > 0, ∀ᶠ n in atTop, ∀ j ≤ Nc + r, ∀ x,
      ‖iteratedFDeriv ℝ j ((defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W aRep) s) x‖ ≤ ε)
    (hcm : ∀ n r', Measurable fun s => coarseCoeff n W r'
      (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s))
    {ord : ℕ} (hordE : ord + 1 ≤ kc + 1 + (Nc + D)) {X Eb : ℝ} (hX : 0 ≤ X) (hEb : 0 ≤ Eb)
    (hPB : ∀ n, ∫⁻ t in Set.Icc tp (tp + Tobs), (∑ j ∈ Finset.range (r + 1), ∑ w' : DerivativeWord2
        j,
          scalInt π (fun x => rs ^ j • orderedDerivative w' (fun x' =>
            ∑ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), deriv (F.weight (pp k)) t •
              pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ
                  m)
                (ocDStar q Λ m ν B / ρ) Nc H (Cc k)
                (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                (coarseTraj n W) t x') x)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal X * classicalStrongEnergy ρ B π (Set.Icc tp (tp
          + Tobs)) ord (coarseTraj n W))
    (hEn : strongEnergyUpTo ρ B π tp (tp + Tobs) ord W ≤
        ENNReal.ofReal Eb)
    (hβ : IntegrableOn (fun s => Real.sqrt (2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m'
        (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) * (∑ v,
              (π v)⁻¹ * gradFactorialNormSqUpTo ρ m' (W v s).val) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2) * massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h
              v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v s).val))))) (Set.Icc tp (tp +
                Tobs))) :
    ∫ s in Set.Icc tp (tp + Tobs), Real.sqrt (massNormSq (E := h) (K := Kc) rs π (fun v => (qq s
        v).val)) ≤
      (∫ s in Set.Icc tp (tp + Tobs), Real.sqrt (2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m'
          (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) * (∑ v,
              (π v)⁻¹ * gradFactorialNormSqUpTo ρ m' (W v s).val) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2) * massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h
              v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v s).val))))) + X * Eb := by
  have hπ := w.hcs.mass_pos
  have hrK : r ≤ Klift := by omega
  refine integral_sqrt_massNormSq_le_of_split measurableSet_Icc Kc rs π hπ
    (fun n s v => carrierOf (Kc v) (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v s x))
    (fun n s v => carrierOf (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
          tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) s x v))
    (fun n s v => carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k
        => F.weight (pp k)) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W
              aRep) s x v))
    (fun n s v => carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k
        => deriv (F.weight (pp k))) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) s x v)) qq
    (fun n s hs v => w.approxForce_carrier_eq hAcl hK hrL hord hNco Vc Vn hch n hs Kc hKr v)
    hqlim hqm (fun s => Real.sqrt_nonneg _) hβ (fun n s hs => ?_)
    (fun s hs v => w.defectLift_carrier_tendsto hrK hrL hNco Kc hKr hs (hE0 s hs) v)
    (fun n v => w.partition_carrier_aesm n hrK hrL (hcm n) Kc hKr v) (mul_nonneg hX hEb)
    (fun n => ?_)
  · exact Real.sqrt_le_sqrt (w.approxResForce_carrier_mass_le_sep hSb hAcl hK hrL hord hk hNχ
      hNχ' hCg hgr Vc Vn hch hkres hmr n hs hrs hrse Kc hKr)
  · refine (w.partition_mass_integral_le hrK hrL Kc hKr hrs.le hordE hPB n).trans ?_
    rw [ENNReal.ofReal_mul hX]
    exact mul_le_mul_right hEn _

end AVRegularity.CycleComparison.Reconstruction
end
