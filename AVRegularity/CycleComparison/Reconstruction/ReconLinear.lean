-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.ReconPeriodic
import AVRegularity.CycleComparison.Reconstruction.ClassicalBridge
import AVRegularity.CycleComparison.Reconstruction.Continuity
public import AVRegularity.CycleComparison.Reconstruction.PartitionBound
import AVRegularity.CycleComparison.Lift.SettingConstructedLiftSequence
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.TailJets

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The mass-weighted norms of the residual carriers at one time of the window**.
Summing the word bounds `ReconWindowAt.resFlux_word_le`, `ReconWindowAt.resForce_word_le` over
the derivative words of order `≤ r`
(`sum_words_le`), the mass-weighted factorial norm at the radius `rs` of the carrier of the
residual flux (`ReconWindowAt.resFlux_mass_le`) and of the residual force
(`ReconWindowAt.resForce_mass_le`) of a coarse field `u` and a flux field `G` is bounded by the
gradient energy density of `u` and the jet density of `G`. -/

/-- A uniform bound of the terms of the derivative words of order `≤ r` bounds their sum by
`2^{r+1}` times the bound. -/
theorem sum_words_le (f : ∀ j : ℕ, DerivativeWord2 j → ℝ≥0∞) (r : ℕ) {Bd : ℝ≥0∞}
    (hf : ∀ j, j ≤ r → ∀ β, f j β ≤ Bd) :
    ∑ j ∈ Finset.range (r + 1), ∑ β : DerivativeWord2 j, f j β ≤ 2 ^ (r + 1) * Bd := by
  have hgeom : ∀ n : ℕ, ∑ j ∈ Finset.range n, (2 : ℝ≥0∞) ^ j ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ, mul_two]
      exact add_le_add_left ih _
  calc ∑ j ∈ Finset.range (r + 1), ∑ β : DerivativeWord2 j, f j β
      ≤ ∑ j ∈ Finset.range (r + 1), ∑ _β : DerivativeWord2 j, Bd :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun β _ =>
          hf j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) β
    _ = (∑ j ∈ Finset.range (r + 1), (2 : ℝ≥0∞) ^ j) * Bd := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_const, card_derivativeWord2, nsmul_eq_mul]
        push_cast
        rfl
    _ ≤ 2 ^ (r + 1) * Bd := mul_le_mul_left (hgeom (r + 1)) _

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
variable {P' : Type*} {Ctx : P' → Type*}
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

/-- **The mass-weighted norm of the carrier of the residual flux at one time of the window.** -/
theorem ReconWindowAt.resFlux_mass_le
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
    (u : ℝ → Vec 2 → ∀ i, h i) (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain (Acl + 2 + r) (r + 1) Acl
        (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
          (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
            (ρ • X))) τ)
        (tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ
            (Φ (m - 1)) hφ ν B ρ
            (ρ / ocEpsilon q Λ (m - 1)) k
            (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
          (ocDStar q Λ m ν B / ρ)
          (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
            (ρ • X))) τ)
        (fun j => Vc k hh j τ))
    (G : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
    (hG : ∀ s' k', ContDiff ℝ ((kres + 2 : ℕ) : ℕ∞) (fun x => G s' x k'))
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hVn : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain (Acl + 2 + r) (max (Llift + 1) (Llift + 2)) Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
          fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k')
            (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
              (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k'))
          τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n' j τ))
    {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (hu : ContDiff ℝ ((m' + 1 : ℕ) : ℕ∞) (u t))
    (hup : IsZ2Periodic (u t)) (hGp : ∀ k', IsZ2Periodic (fun x => G t x k'))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m)
    (hrsρ : rs ≤ ρ)
    (K : ι → ℕ) (hKr : ∀ v, K v ≤ r)
    (hfv : ∀ v, ContDiff ℝ (K v : ℕ∞) (fun x => (WithLp.toLp 2 (fun a₀ =>
      reconResFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Vc Vn G t x a₀ v) : PiLp 2 (fun _ : Fin 2 => h v))))
    (hfvp : ∀ v, IsZ2Periodic (fun x => (WithLp.toLp 2 (fun a₀ =>
      reconResFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Vc Vn G t x a₀ v) : PiLp 2 (fun _ : Fin 2 => h v)))) :
    ENNReal.ofReal (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) rs π
        (fun v => (periodicHk (K v) _ (hfv v) (hfvp v)).val)) ≤
      2 ^ (r + 1) * (3 * (ENNReal.ofReal (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ)) *
          ENNReal.ofReal (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) *
          ResidualTimeData.gradDensity π ρ m' u t +
        ENNReal.ofReal (((r.factorial : ℝ)) ^ 2) *
          CoarseFluxDiff.fluxDensity ρ kres π G t +
        ENNReal.ofReal (liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ)) *
          ENNReal.ofReal ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2) *
          CoarseFluxDiff.fluxDensity ρ kres π G t)) := by
  have hT := (w.glued_tail_contDiff hAcl hK hrL hord u Vc hV ht hu).1
  have hL := (w.glued_lift_contDiff hAcl hrL G Vn hVn ht).1
  have hF : ContDiff ℝ (r : ℕ∞) (fun x a₀ => reconResFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Vc Vn G t x a₀) :=
    contDiff_pi.2 fun a₀ => ((hT a₀).add ((hG t a₀).of_le (by exact_mod_cast
      (by omega : r ≤ kres + 2)))).add (hL a₀)
  refine (massNormSq_periodicHk_flux_le K hKr hrs.le π w.hcs.mass_pos _ hF hfv hfvp).trans ?_
  refine sum_words_le _ r fun j hj β => ?_
  refine (w.resFlux_word_le hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr u Vc hV G hG Vn hVn ht hu
    hup hGp hrs hrse hrsρ hj β).trans ?_
  refine mul_le_mul_right (add_le_add (add_le_add le_rfl ?_) le_rfl) 3
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have h1 : ((j.factorial : ℕ) : ℝ) ≤ ((r.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le hj
  exact pow_le_pow_left₀ (by positivity) h1 2

/-- **The mass-weighted norm of the carrier of the residual force at one time of the window.** -/
theorem ReconWindowAt.resForce_mass_le
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
    (u : ℝ → Vec 2 → ∀ i, h i) (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain (Acl + 2 + r) (r + 1) Acl
        (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
          (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
            (ρ • X))) τ)
        (tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ
            (Φ (m - 1)) hφ ν B ρ
            (ρ / ocEpsilon q Λ (m - 1)) k
            (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
          (ocDStar q Λ m ν B / ρ)
          (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
            (ρ • X))) τ)
        (fun j => Vc k hh j τ))
    (G : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
    (hG : ∀ s' k', ContDiff ℝ ((kres + 2 : ℕ) : ℕ∞) (fun x => G s' x k'))
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hVn : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain (Acl + 2 + r) (max (Llift + 1) (Llift + 2)) Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
          fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k')
            (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
              (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k'))
          τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n' j τ))
    {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (hu : ContDiff ℝ ((m' + 1 : ℕ) : ℕ∞) (u t))
    (hup : IsZ2Periodic (u t)) (hGp : ∀ k', IsZ2Periodic (fun x => G t x k'))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m)
    (K : ι → ℕ) (hKr : ∀ v, K v ≤ r)
    (hqv : ∀ v, ContDiff ℝ (K v : ℕ∞) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Vc Vn t x v))
    (hqvp : ∀ v, IsZ2Periodic (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Vc Vn t x v)) :
    ENNReal.ofReal (massNormSq (E := h) (K := K) rs π
        (fun v => (periodicHk (K v) _ (hqv v) (hqvp v)).val)) ≤
      2 ^ (r + 1) * (2 * (ENNReal.ofReal (tailForceConst H Nc D Acl r m' (pulseChartD Nχ)) *
          ENNReal.ofReal (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) *
          ResidualTimeData.gradDensity π ρ m' u t +
        ENNReal.ofReal (liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ)) *
          ENNReal.ofReal ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2) *
          CoarseFluxDiff.fluxDensity ρ kres π G t)) := by
  have hT := (w.glued_tail_contDiff hAcl hK hrL hord u Vc hV ht hu).2
  have hL := (w.glued_lift_contDiff hAcl hrL G Vn hVn ht).2
  have hq : ContDiff ℝ (r : ℕ∞) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Vc Vn t x) := hT.add hL
  refine (massNormSq_periodicHk_scal_le K hKr hrs.le π w.hcs.mass_pos _ hq hqv hqvp).trans ?_
  exact sum_words_le _ r fun j hj β => w.resForce_word_le hSb hAcl hK hrL hord hk hNχ hNχ' hCg
    hgr u Vc hV G hG Vn hVn ht hu hup hGp hrs hrse hj β

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The densities of the Galerkin approximants**. The gradient energy density of
the approximant `a_n` and the jet density of the flux approximant `S_n F_c` are the truncated
factorial norms of the Galerkin cutoffs `S_n W(t)` and `S_n F_c(t)`; the cutoff contracts them,
so they are bounded by the densities of the retained field and the norms of the flux
(`gradDensity_coarseTraj_le`, `fluxDensity_fluxApprox_le`). The densities of the differences of
two approximants are bounded by the squared norms of the differences of the cutoffs
(`gradDensity_coarseTraj_sub_le`, `fluxDensity_fluxApprox_sub_le`). -/

section Single

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The classical factorial density of a pair is the sum of those of its components. -/
theorem classicalFactorialSq_toLp (ρ : ℝ) (m : ℕ) (g : Vec 2 → Fin 2 → E)
    (hg : ∀ k, ContDiff ℝ (m : ℕ∞) (fun x => g x k)) :
    classicalFactorialSq ρ m (fun x => (WithLp.toLp 2 (fun k => g x k) :
        PiLp 2 (fun _ : Fin 2 => E))) =
      ∑ k : Fin 2, classicalFactorialSq ρ m (fun x => g x k) := by
  have hpi : ContDiff ℝ (m : ℕ∞) (fun x k => g x k) := contDiff_pi.2 hg
  set L : (Fin 2 → E) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => E)).symm.toContinuousLinearMap with hL
  have hd : ∀ j, j ≤ m → ∀ (w : DerivativeWord2 j) (x : Vec 2),
      ‖orderedDerivative w (fun x => (WithLp.toLp 2 (fun k => g x k) :
        PiLp 2 (fun _ : Fin 2 => E))) x‖ₑ ^ 2 =
        ∑ k : Fin 2, ‖orderedDerivative w (fun x => g x k) x‖ₑ ^ 2 := by
    intro j hj w x
    have hjm : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((m : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hj
    have h1 : orderedDerivative w (fun x => L (fun k => g x k)) =
        fun x => L (orderedDerivative w (fun x k => g x k) x) :=
      orderedDerivative_clm_comp L w (hpi.of_le hjm)
    have h2 : ∀ k, orderedDerivative w (fun x k => g x k) x k =
        orderedDerivative w (fun x => g x k) x := fun k =>
      (congrFun (orderedDerivative_clm_comp (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 2 => E) k) w (hpi.of_le hjm)) x).symm
    have h3 : orderedDerivative w (fun x => (WithLp.toLp 2 (fun k => g x k) :
        PiLp 2 (fun _ : Fin 2 => E))) x =
        WithLp.toLp 2 (fun k => orderedDerivative w (fun x => g x k) x) := by
      have h4 := congrFun h1 x
      simp only [hL, ContinuousLinearEquiv.coe_coe,
        PiLp.continuousLinearEquiv_symm_apply] at h4
      rw [h4]
      congr 1
      funext k
      exact h2 k
    rw [h3, enorm_toLp_sq]
  unfold classicalFactorialSq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hjm' : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((m : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hjm
  simp_rw [hd j hjm w]
  exact lintegral_finsetSum' _ fun k _ =>
    ((continuous_orderedDerivative w ((hg k).of_le hjm')).enorm.measurable.pow_const
      2).aemeasurable

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The truncated gradient factorial norm is at most the largest weight times the squared
norm. -/
theorem gradFactorialNormSqUpTo_le_norm_sq {μ : Measure (Vec 2)} [MeasurableSpace E] {K : ℕ}
    (ρ : ℝ) (m : ℕ) (X : JetL2 μ K E) :
    gradFactorialNormSqUpTo ρ m X ≤ factorialWeightMax ρ K * ‖X‖ ^ 2 := by
  rw [jet_norm_sq_eq_sum, Finset.mul_sum]
  unfold gradFactorialNormSqUpTo
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with hj
  · refine mul_le_mul_of_nonneg_right ?_ (derivativeNormSq_nonneg X j)
    exact factorialWeight_le_max ρ ⟨j.val - 1, by omega⟩
  · exact mul_nonneg ((factorialWeight_nonneg ρ 0).trans
      (factorialWeight_le_max ρ (0 : Fin (K + 1)))) (derivativeNormSq_nonneg X j)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The truncated factorial norm is at most the largest weight times the squared norm. -/
theorem factorialNormSqUpTo_le_norm_sq {μ : Measure (Vec 2)} [MeasurableSpace E] {K : ℕ}
    (ρ : ℝ) (m : ℕ) (X : JetL2 μ K E) :
    factorialNormSqUpTo ρ m X ≤ factorialWeightMax ρ K * ‖X‖ ^ 2 := by
  rw [jet_norm_sq_eq_sum, Finset.mul_sum]
  unfold factorialNormSqUpTo
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with hj
  · exact mul_le_mul_of_nonneg_right (factorialWeight_le_max ρ j) (derivativeNormSq_nonneg X j)
  · exact mul_nonneg ((factorialWeight_nonneg ρ 0).trans
      (factorialWeight_le_max ρ (0 : Fin (K + 1)))) (derivativeNormSq_nonneg X j)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The truncated factorial norm is at most the factorial norm. -/
theorem factorialNormSqUpTo_le_factorialNormSq' {μ : Measure (Vec 2)} [MeasurableSpace E]
    {K : ℕ} (ρ : ℝ) (m : ℕ) (X : JetL2 μ K E) :
    factorialNormSqUpTo ρ m X ≤ factorialNormSq ρ X := by
  unfold factorialNormSqUpTo factorialNormSq
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (factorialWeight_nonneg _ _) (derivativeNormSq_nonneg X j)

end Single

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The gradient energy density of the approximant** is that of the Galerkin cutoffs. -/
theorem gradDensity_coarseTraj_eq (π : ι → ℝ) (ρ : ℝ) {m r K : ℕ} (hmr : m + 1 ≤ r)
    (hrK : r ≤ K) (n : ℕ) (W : ∀ v, ℝ → TorusHk K (h v)) (t : ℝ) :
    ResidualTimeData.gradDensity π ρ m (coarseTraj n W) t = ∑ v, ENNReal.ofReal (π v)⁻¹ *
      ENNReal.ofReal (gradFactorialNormSqUpTo ρ m (galerkinProj n (W v t)).val) := by
  unfold ResidualTimeData.gradDensity
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  rw [coarseTraj_eq]
  exact classicalGradFactorialSq_eq_of_rep (coarseApprox_isClassicalRep n (fun u => W u t) v hrK)
    ρ hmr

/-- **The gradient energy density of the approximant is at most that of the retained field.** -/
theorem gradDensity_coarseTraj_le (π : ι → ℝ) (ρ : ℝ) {m r K : ℕ} (hmr : m + 1 ≤ r)
    (hrK : r ≤ K) (n : ℕ) (W : ∀ v, ℝ → TorusHk K (h v)) (aRep : ℝ → Vec 2 → ∀ i, h i)
    {t : ℝ} (ha : ∀ v, IsClassicalRep (W v t) (fun x => aRep t x v) r) :
    ResidualTimeData.gradDensity π ρ m (coarseTraj n W) t ≤
      ResidualTimeData.gradDensity π ρ m aRep t := by
  rw [gradDensity_coarseTraj_eq π ρ hmr hrK n W t]
  unfold ResidualTimeData.gradDensity
  refine Finset.sum_le_sum fun v _ => ?_
  rw [classicalGradFactorialSq_eq_of_rep (ha v) ρ hmr]
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
    (gradFactorialNormSqUpTo_galerkinProj_le n ρ m (W v t))) _

/-- **The gradient energy density of a difference of approximants** is at most the largest
weight times the squared norms of the differences of the cutoffs. -/
theorem gradDensity_coarseTraj_sub_le (π : ι → ℝ) (ρ : ℝ) {m r K : ℕ} (hmr : m + 1 ≤ r)
    (hrK : r ≤ K) (n n' : ℕ) (W : ∀ v, ℝ → TorusHk K (h v)) (t : ℝ) :
    ResidualTimeData.gradDensity π ρ m
        (fun s x => coarseTraj n W s x - coarseTraj n' W s x) t ≤
      ∑ v, ENNReal.ofReal (π v)⁻¹ * ENNReal.ofReal (factorialWeightMax ρ K *
        ‖galerkinProj n (W v t) - galerkinProj n' (W v t)‖ ^ 2) := by
  unfold ResidualTimeData.gradDensity
  refine Finset.sum_le_sum fun v _ => mul_le_mul_right ?_ _
  have hrep := isClassicalRep_sub (coarseApprox_isClassicalRep n (fun u => W u t) v hrK)
    (coarseApprox_isClassicalRep n' (fun u => W u t) v hrK)
  have e : (fun x => (coarseTraj n W t x - coarseTraj n' W t x) v) =
      fun x => coarseApprox n (fun u => W u t) x v - coarseApprox n' (fun u => W u t) x v := by
    funext x
    rw [coarseTraj_eq, coarseTraj_eq]
    rfl
  rw [e, classicalGradFactorialSq_eq_of_rep hrep ρ hmr]
  exact ENNReal.ofReal_le_ofReal (gradFactorialNormSqUpTo_le_norm_sq ρ m _)

/-- **The jet density of the flux approximant** is at most the mass-weighted factorial norm of
the flux. -/
theorem fluxDensity_fluxApprox_le (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (ρ : ℝ) {m k : ℕ}
    (hmk : m ≤ k) (n : ℕ) (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (t : ℝ) :
    CoarseFluxDiff.fluxDensity ρ m π (fun s x a₀ => fluxApprox n (fun v => Fc v s) x a₀) t ≤
      ENNReal.ofReal (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
        (K := fun _ => k) ρ π (fun v => (Fc v t).val)) := by
  unfold CoarseFluxDiff.fluxDensity massNormSq
  rw [ENNReal.ofReal_sum_of_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
    (factorialNormSq_nonneg ρ _)]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)]
  refine mul_le_mul_right ?_ _
  have hc : ∀ a₀ : Fin 2, ContDiff ℝ (m : ℕ∞)
      (fun x => fluxApprox n (fun v => Fc v t) x a₀ v) := fun a₀ =>
    (contDiff_pi.1 (fluxApprox_contDiff n (fun v => Fc v t) a₀) v).of_le
      (by exact_mod_cast le_top)
  rw [← classicalFactorialSq_toLp ρ m (fun x a₀ => fluxApprox n (fun v => Fc v t) x a₀ v) hc,
    classicalFactorialSq_eq_of_rep (fluxApprox_isClassicalRep n (fun v => Fc v t) v hmk) ρ
      le_rfl]
  refine ENNReal.ofReal_le_ofReal ((factorialNormSqUpTo_galerkinProj_le n ρ m (Fc v t)).trans ?_)
  exact factorialNormSqUpTo_le_factorialNormSq' ρ m _

/-- **The jet density of a difference of flux approximants** is at most the largest weight
times the squared norms of the differences of the cutoffs. -/
theorem fluxDensity_fluxApprox_sub_le (π : ι → ℝ) (ρ : ℝ) {m k : ℕ} (hmk : m ≤ k) (n n' : ℕ)
    (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (t : ℝ) :
    CoarseFluxDiff.fluxDensity ρ m π (fun s x a₀ => fluxApprox n (fun v => Fc v s) x a₀ -
        fluxApprox n' (fun v => Fc v s) x a₀) t ≤
      ∑ v, ENNReal.ofReal (π v)⁻¹ * ENNReal.ofReal (factorialWeightMax ρ k *
        ‖galerkinProj n (Fc v t) - galerkinProj n' (Fc v t)‖ ^ 2) := by
  unfold CoarseFluxDiff.fluxDensity
  refine Finset.sum_le_sum fun v _ => mul_le_mul_right ?_ _
  have hc : ∀ a₀ : Fin 2, ContDiff ℝ (m : ℕ∞) (fun x => (fluxApprox n (fun v => Fc v t) x a₀ -
      fluxApprox n' (fun v => Fc v t) x a₀) v) := fun a₀ =>
    ((contDiff_pi.1 (fluxApprox_contDiff n (fun v => Fc v t) a₀) v).sub
      (contDiff_pi.1 (fluxApprox_contDiff n' (fun v => Fc v t) a₀) v)).of_le
      (by exact_mod_cast le_top)
  rw [← classicalFactorialSq_toLp ρ m (fun x a₀ => (fluxApprox n (fun v => Fc v t) x a₀ -
    fluxApprox n' (fun v => Fc v t) x a₀) v) hc]
  have hrep := isClassicalRep_sub (fluxApprox_isClassicalRep n (fun v => Fc v t) v hmk)
    (fluxApprox_isClassicalRep n' (fun v => Fc v t) v hmk)
  have e : (fun x => (WithLp.toLp 2 (fun a₀ => (fluxApprox n (fun v => Fc v t) x a₀ -
      fluxApprox n' (fun v => Fc v t) x a₀) v) : PiLp 2 (fun _ : Fin 2 => h v))) =
      fun x => WithLp.toLp 2 (fun j => fluxApprox n (fun v => Fc v t) x j v) -
        WithLp.toLp 2 (fun j => fluxApprox n' (fun v => Fc v t) x j v) := by
    funext x
    rfl
  rw [e, classicalFactorialSq_eq_of_rep hrep ρ le_rfl]
  exact ENNReal.ofReal_le_ofReal (factorialNormSqUpTo_le_norm_sq ρ m _)

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Differences of the cleanup chains on a reconstruction window**. The
differences of the tail chains of two smooth coarse fields are tail chains of the difference of
the fields (`ReconWindowAt.tail_chains_sub`), and the differences of the lift chains of the
divergences of two smooth flux fields are lift chains of the divergence of the difference
(`ReconWindowAt.lift_chains_sub`): the chain data are linear in the field
(`tailScalarField_sub_input`, `tailFluxField_sub_input`, `liftApply_sub_input`) and the
difference of two chains is a chain of the difference of the data (`IsCleanupChain.sub`). -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
variable {P' : Type*} {Ctx : P' → Type*}
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

/-- **Differences of tail chains are tail chains of the difference.** -/
theorem ReconWindowAt.tail_chains_sub
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {sXc sZc Acl : ℕ} (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc) (hX : sXc ≤ Klift + D + 2)
    (hZ : sZc ≤ max (Llift + 1) (Llift + 2)) (u u' : ℝ → Vec 2 → ∀ i, h i)
    (hu : ∀ s', ContDiff ℝ (⊤ : ℕ∞) (u s')) (hu' : ∀ s', ContDiff ℝ (⊤ : ℕ∞) (u' s'))
    (Vc Vc' : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXc sZc Acl
        (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
          (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
            (ρ • X))) τ)
        (tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ
            (Φ (m - 1)) hφ ν B ρ
            (ρ / ocEpsilon q Λ (m - 1)) k
            (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
          (ocDStar q Λ m ν B / ρ)
          (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
            (ρ • X))) τ)
        (fun j => Vc k hh j τ)))
    (hV' : (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXc sZc Acl
        (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
          (fun s' X => u' (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
            (ρ • X))) τ)
        (tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ
            (Φ (m - 1)) hφ ν B ρ
            (ρ / ocEpsilon q Λ (m - 1)) k
            (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
          (ocDStar q Λ m ν B / ρ)
          (fun s' X => u' (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
            (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
            (ρ • X))) τ)
        (fun j => Vc' k hh j τ))) :
    (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXc sZc Acl
        (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
          (fun s' X => (fun s x => u s x - u' s x) (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m -
              1)) hφ
            (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
            (ρ • X))) τ)
        (tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ
            (Φ (m - 1)) hφ ν B ρ
            (ρ / ocEpsilon q Λ (m - 1)) k
            (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
          (ocDStar q Λ m ν B / ρ)
          (fun s' X => (fun s x => u s x - u' s x) (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m -
              1)) hφ
            (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
            (ρ • X))) τ)
        (fun j => (fun k hh j τ X z a => Vc k hh j τ X z a - Vc' k hh j τ X z a) k hh j τ)) := by
  intro k hk hh hhh τ hτ
  have P := w.hsetting k hk
  have hseq := w.hseq k hk
  set A : ℝ → Vec 2 → ∀ i, h i := fun s' X => u (ocEll q Λ m ν ^ 2 * s')
    (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
      (ρ • X)) with hAdef
  set A' : ℝ → Vec 2 → ∀ i, h i := fun s' X => u' (ocEll q Λ m ν ^ 2 * s')
    (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
      (ρ • X)) with hA'def
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun X : Vec 2 => ocChart α q Λ m (Φ (m - 1)) hφ
      (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * τ)
        (ρ • X)) :=
    (contDiff_ocChart hφ α q Λ m _ _).comp (contDiff_const_smul _)
  have hA : ContDiff ℝ (⊤ : ℕ∞) (A τ) := (hu _).comp hχ
  have hA' : ContDiff ℝ (⊤ : ℕ∞) (A' τ) := (hu' _).comp hχ
  have hpres := fun (n : ℕ) (hn1 : Nc + 1 ≤ n) (hn2 : n ≤ 2 * Nc + D) =>
    setting_tail_presentation P (Klift + D + 2) (max (Llift + 1) (Llift + 2)) (by omega)
      (by omega) (Cc k) hseq hh hhh n (by omega) hn2
  have hF := (isBoxSmooth_tailFluxField_of_presentation (f := fun _ => 0)
    (F := fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
      ρ (ρ / ocEpsilon q Λ (m - 1))
      k (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) hpres
    (ocDStar q Λ m ν B / ρ) A hτ hA).mono hX hZ
  have hF' := (isBoxSmooth_tailFluxField_of_presentation (f := fun _ => 0)
    (F := fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
      ρ (ρ / ocEpsilon q Λ (m - 1))
      k (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) hpres
    (ocDStar q Λ m ν B / ρ) A' hτ hA').mono hX hZ
  have hS := IsCleanupChain.sub hXc hZc hF hF' (hV k hk hh hhh τ hτ) (hV' k hk hh hhh τ hτ)
  have e1 : tailScalarField (fun _ => 0) Nc D
      (ocDStar q Λ m ν B / ρ) (fun s' X => A s' X - A' s' X) τ =
      fun X z => tailScalarField (fun _ => 0) Nc D
          (ocDStar q Λ m ν B / ρ) A τ X z -
        tailScalarField (fun _ => 0) Nc D
          (ocDStar q Λ m ν B / ρ) A' τ X z :=
    funext₂ fun X z => tailScalarField_sub_input _ _ _ _ A A' τ
      (hA.of_le (by exact_mod_cast le_top)) (hA'.of_le (by exact_mod_cast le_top)) X z
  have e2 : tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ
      (Φ (m - 1)) hφ ν B ρ
      (ρ / ocEpsilon q Λ (m - 1)) k
      (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
      (ocDStar q Λ m ν B / ρ) (fun s' X => A s' X - A' s' X) τ =
      fun X z a => tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ
          (Φ (m - 1)) hφ ν B ρ
          (ρ / ocEpsilon q Λ (m - 1)) k
          (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
          (ocDStar q Λ m ν B / ρ) A τ X z a -
        tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ
          (Φ (m - 1)) hφ ν B ρ
          (ρ / ocEpsilon q Λ (m - 1)) k
          (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
          (ocDStar q Λ m ν B / ρ) A' τ X z a := by
    funext X z a
    exact tailFluxField_sub_input _ _ _ _ A A' τ (hA.of_le (by exact_mod_cast le_top))
      (hA'.of_le (by exact_mod_cast le_top)) X z a
  show IsCleanupChain sXc sZc Acl (tailScalarField (fun _ => 0) Nc D
      (ocDStar q Λ m ν B / ρ) (fun s' X => A s' X - A' s' X) τ)
    (tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ
      (Φ (m - 1)) hφ ν B ρ
      (ρ / ocEpsilon q Λ (m - 1)) k
      (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
      (ocDStar q Λ m ν B / ρ) (fun s' X => A s' X - A' s' X) τ)
    (fun j X z a => Vc k hh j τ X z a - Vc' k hh j τ X z a)
  rw [e1, e2]
  exact hS

/-- **Differences of lift chains are lift chains of the difference.** -/
theorem ReconWindowAt.lift_chains_sub
    (_w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {sXl sZl Acl : ℕ} (hXl : 1 ≤ sXl) (hZl : 1 ≤ sZl) (G G' : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
    (hG : ∀ s' k', ContDiff ℝ (⊤ : ℕ∞) (fun x => G s' x k'))
    (hG' : ∀ s' k', ContDiff ℝ (⊤ : ℕ∞) (fun x => G' s' x k'))
    (Vn Vn' : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXl sZl Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
          fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k')
            (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
              (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k'))
          τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n' j τ)))
    (hV' : (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXl sZl Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
          fderiv ℝ (fun x => G' (ocEll q Λ m ν ^ 2 * s') x k')
            (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
              (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k'))
          τ)
        (fun _ _ _ => 0) (fun j => Vn' k hh n' j τ))) :
    (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXl sZl Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
          fderiv ℝ (fun x => (fun s x a => G s x a - G' s x a) (ocEll q Λ m ν ^ 2 * s') x k')
            (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
              (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k'))
          τ)
        (fun _ _ _ => 0) (fun j => (fun k hh n j τ X z a => Vn k hh n j τ X z a - Vn' k hh n j τ X z
            a) k hh n' j τ)) := by
  intro k hk hh hhh n' hn' τ hτ
  have hS := IsCleanupChain.sub hXl hZl (isBoxSmooth_zero sXl sZl) (isBoxSmooth_zero sXl sZl)
    (hV k hk hh hhh n' hn' τ hτ) (hV' k hk hh hhh n' hn' τ hτ)
  set A : ℝ → Vec 2 → ∀ i, h i := fun s' X => ∑ k' : Fin 2,
    fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k')
      (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
        (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k') with hAdef
  set A' : ℝ → Vec 2 → ∀ i, h i := fun s' X => ∑ k' : Fin 2,
    fderiv ℝ (fun x => G' (ocEll q Λ m ν ^ 2 * s') x k')
      (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
        (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k') with hA'def
  have hχ : ∀ s', ContDiff ℝ (⊤ : ℕ∞) (fun X : Vec 2 => ocChart α q Λ m (Φ (m - 1)) hφ
      (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
        (ρ • X)) := fun s' =>
    (contDiff_ocChart hφ α q Λ m _ _).comp (contDiff_const_smul _)
  have hdiv : ∀ (Gf : ℝ → Vec 2 → Fin 2 → ∀ i, h i),
      (∀ s' k', ContDiff ℝ (⊤ : ℕ∞) (fun x => Gf s' x k')) → ∀ s',
      ContDiff ℝ (⊤ : ℕ∞) (fun X => ∑ k' : Fin 2,
        fderiv ℝ (fun x => Gf (ocEll q Λ m ν ^ 2 * s') x k')
          (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
            (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k')) :=
    fun Gf hGf s' => ContDiff.sum fun k' _ =>
      (((hGf _ k').fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp (hχ s')).clm_apply contDiff_const
  have hAd : ∀ s' X, A s' X - A' s' X = ∑ k' : Fin 2,
      fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k' - G' (ocEll q Λ m ν ^ 2 * s') x k')
        (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
          (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k') := by
    intro s' X
    simp only [hAdef, hA'def]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [fderiv_fun_sub (((hG _ k').differentiable (by simp)) _)
      (((hG' _ k').differentiable (by simp)) _)]
    rfl
  have hfun : (fun s' X => ∑ k' : Fin 2,
      fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k' - G' (ocEll q Λ m ν ^ 2 * s') x k')
        (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
          (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k')) =
      fun s' X => A s' X - A' s' X := funext₂ fun s' X => (hAd s' X).symm
  have e1 : liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => A s' X - A' s' X) τ =
      fun X z => liftApply (n' + 1) (Cc k hh (n' + 1)) A τ X z -
        liftApply (n' + 1) (Cc k hh (n' + 1)) A' τ X z :=
    funext₂ fun X z => liftApply_sub_input (n' + 1) (Cc k hh (n' + 1)) A A' τ
      ((hdiv G hG τ).of_le (by exact_mod_cast le_top))
      ((hdiv G' hG' τ).of_le (by exact_mod_cast le_top)) X z
  show IsCleanupChain sXl sZl Acl (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
      fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k' - G' (ocEll q Λ m ν ^ 2 * s') x k')
        (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
          (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k')) τ)
    (fun _ _ _ => 0) (fun j X z a => Vn k hh n' j τ X z a - Vn' k hh n' j τ X z a)
  rw [hfun, e1]
  convert hS using 1
  funext X z a
  simp
end

/-! **Linearity of the glued residual and the chains of the approximants**. The
glued residual flux and force of differences of chains and flux fields are the differences of
the glued residuals (`reconResFlux_sub`, `reconResForce_sub'`), and the lift chains of the
approximants (`ReconWindowAt.IsApproxChains`) are lift chains of the divergence of the flux
approximant in the form of the slices (`ReconWindowAt.IsApproxChains.lift_div`). -/

section
section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The glued tail flux of a difference of chains. -/
theorem gluedTailFlux_sub_chain (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ)
    (ψs : ℤ → ℝ → Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vc Vc' : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ) (x : Vec 2) (a₀ : Fin 2) :
    gluedTailFlux kset ϖ ψs H N Acl ε c ρs es
        (fun k hh j τ X z a => Vc k hh j τ X z a - Vc' k hh j τ X z a) t x a₀ =
      gluedTailFlux kset ϖ ψs H N Acl ε c ρs es Vc t x a₀ -
        gluedTailFlux kset ϖ ψs H N Acl ε c ρs es Vc' t x a₀ := by
  simp only [gluedTailFlux, ← Finset.sum_sub_distrib, ← smul_sub]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← tailFluxPhys_sub_chain]

/-- The glued lifted flux of a difference of chains. -/
theorem gluedLiftFlux_sub_chain (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ)
    (ψs : ℤ → ℝ → Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vn Vn' : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ) (x : Vec 2)
    (a₀ : Fin 2) :
    gluedLiftFlux kset ϖ ψs H N Acl ε c ρs es
        (fun k hh n j τ X z a => Vn k hh n j τ X z a - Vn' k hh n j τ X z a) t x a₀ =
      gluedLiftFlux kset ϖ ψs H N Acl ε c ρs es Vn t x a₀ -
        gluedLiftFlux kset ϖ ψs H N Acl ε c ρs es Vn' t x a₀ := by
  simp only [gluedLiftFlux, ← Finset.sum_sub_distrib, ← smul_sub]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← liftFluxPhys_sub_chain]

end Linear

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **The glued residual flux of differences is the difference of the glued residual fluxes.** -/
theorem reconResFlux_sub (α q : ℝ) (Λ m : ℕ) (φs : ℝ → Vec 2 → ℝ)
    (hφs : IsAdmissibleStream φs) (ν B ρ tA tZ : ℝ) (ϖ : ℤ → ℝ → ℝ) (H N Acl : ℕ)
    (Vc Vc' : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn Vn' : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (G G' : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) (a₀ : Fin 2) :
    reconResFlux α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl
        (fun k hh j τ X z a => Vc k hh j τ X z a - Vc' k hh j τ X z a)
        (fun k hh n j τ X z a => Vn k hh n j τ X z a - Vn' k hh n j τ X z a)
        (fun s y a => G s y a - G' s y a) t x a₀ =
      reconResFlux α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl Vc Vn G t x a₀ -
        reconResFlux α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl Vc' Vn' G' t x a₀ := by
  simp only [reconResFlux, gluedTailFlux_sub_chain, gluedLiftFlux_sub_chain]
  abel

variable {P' : Type*} {Ctx : P' → Type*}
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

/-- **The lift chains of an approximant in the form of the slices.** -/
theorem ReconWindowAt.IsApproxChains.lift_div
    {{w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀}}
    {n sXc sZc Acl sXl sZl : ℕ} {Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    {Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hch : w.IsApproxChains n sXc sZc Acl sXl sZl Vc Vn) :
    ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXl sZl Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
          fderiv ℝ (fun x => fluxApprox n (fun v => Fc v (ocEll q Λ m ν ^ 2 * s')) x k')
            (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
              (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k'))
          τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n' j τ) := by
  intro k hk hh hhh n' hn' τ hτ
  have h1 := hch.2 k hk hh hhh n' hn' τ hτ
  have e : (fun s' X => fluxApproxDiv n Fc (ocEll q Λ m ν ^ 2 * s')
      ((ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
        (ocEll q Λ m ν ^ 2 * s') (ρ • X))) =
      fun s' X => ∑ k' : Fin 2,
        fderiv ℝ (fun x => fluxApprox n (fun v => Fc v (ocEll q Λ m ν ^ 2 * s')) x k')
          (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
            (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k') :=
    funext₂ fun s' X => fluxApproxDiv_eq_sum_fderiv n Fc _ _
  rw [e] at h1
  exact h1
end

end AVRegularity.CycleComparison.Reconstruction
end
