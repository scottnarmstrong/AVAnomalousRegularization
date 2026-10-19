-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.ReconLinear
public import AVRegularity.CycleComparison.Reconstruction.PartitionBound
public import AVRegularity.CycleComparison.Reconstruction.ReconPeriodic
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.Lift.SettingConstructedLiftSequence
import AVRegularity.CycleComparison.Reconstruction.ClassicalBridge
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.TailJets
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The residual flux carriers of the Galerkin approximants**. At every time of
the window, the residual flux `approxFlux … n` of the `n`-th approximant is of class `C^{K_v}`
and periodic (`ReconWindowAt.approxFlux_smooth`), and the mass-weighted norm of its carrier is
bounded uniformly in `n` by the gradient density of the retained field and the norm of the flux
(`ReconWindowAt.approxFlux_carrier_mass_le_sep`). -/

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

/-- The combination of the slice bounds of the residual flux. -/
theorem ennreal_slice_combine (r : ℕ) {A X B' C' Y g f : ℝ} (hA : 0 ≤ A) (hX : 0 ≤ X)
    (hB : 0 ≤ B') (hC : 0 ≤ C') (hY : 0 ≤ Y) (hg : 0 ≤ g) (hf : 0 ≤ f) {gd fd : ℝ≥0∞}
    (hgd : gd ≤ ENNReal.ofReal g) (hfd : fd ≤ ENNReal.ofReal f) :
    2 ^ (r + 1) * (3 * (ENNReal.ofReal A * ENNReal.ofReal X * gd + ENNReal.ofReal B' * fd +
        ENNReal.ofReal C' * ENNReal.ofReal Y * fd)) ≤
      ENNReal.ofReal (2 ^ (r + 1) * (3 * (A * X + B' + C' * Y)) * (g + f)) := by
  have h1 : 2 ^ (r + 1) * (3 * (ENNReal.ofReal A * ENNReal.ofReal X * gd +
      ENNReal.ofReal B' * fd + ENNReal.ofReal C' * ENNReal.ofReal Y * fd)) ≤
      2 ^ (r + 1) * (3 * (ENNReal.ofReal A * ENNReal.ofReal X * ENNReal.ofReal g +
        ENNReal.ofReal B' * ENNReal.ofReal f + ENNReal.ofReal C' * ENNReal.ofReal Y *
          ENNReal.ofReal f)) := by
    gcongr
  refine h1.trans (le_of_eq_of_le ?_ (ENNReal.ofReal_le_ofReal (show 2 ^ (r + 1) * (3 *
      (A * X * g + B' * f + C' * Y * f)) ≤ 2 ^ (r + 1) * (3 * (A * X + B' + C' * Y)) * (g + f)
    by nlinarith [mul_nonneg hA hX, mul_nonneg hC hY, mul_nonneg (mul_nonneg hA hX) hf,
      mul_nonneg hB hg, mul_nonneg (mul_nonneg hC hY) hg,
      pow_pos (by norm_num : (0 : ℝ) < 2) (r + 1)])))
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity)
      (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- **The residual flux of an approximant is smooth and periodic** at a time of the window. -/
theorem ReconWindowAt.approxFlux_smooth
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r m' : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) :
    (∀ v, ContDiff ℝ (Kc v : ℕ∞) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v t x)) ∧
    (∀ v, IsZ2Periodic (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v t x)) := by
  have hT := (w.glued_tail_contDiff hAcl hK hrL hord (coarseTraj n W) (Vc n) (hch n).1 ht
    ((coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top))).1
  have hL := (w.glued_lift_contDiff hAcl hrL (fun s x a₀ => fluxApprox n (fun v => Fc v s) x a₀)
    (Vn n) (hch n).lift_div ht).1
  have hP := (w.res_periodic hAcl (by omega : 1 ≤ r + 1)
    (by omega : 1 ≤ max (Llift + 1) (Llift + 2)) (coarseTraj n W) (Vc n) (hch n).1
    (fun s x a₀ => fluxApprox n (fun v => Fc v s) x a₀) (Vn n) (hch n).lift_div ht
    (coarseTraj_periodic n W t) (fun k' => fluxApprox_periodic n (fun v => Fc v t) k')).1
  refine ⟨fun v => ?_, fun v l x => ?_⟩
  · refine (contDiff_piLp 2).2 fun a₀ => ?_
    have h1 : ContDiff ℝ (r : ℕ∞) (fun x => reconResFlux α q Λ m (Φ (m - 1)) hφ ν B
        ρ tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl
        (Vc n) (Vn n) (fun s x a₀ => fluxApprox n (fun v => Fc v s) x a₀) t x a₀) :=
      ((hT a₀).add ((fluxApprox_contDiff n (fun v => Fc v t) a₀).of_le
        (by exact_mod_cast le_top))).add (hL a₀)
    exact (contDiff_pi.1 h1 v).of_le (by exact_mod_cast hKr v)
  · show (WithLp.toLp 2 fun a₀ => reconResFlux α q Λ m (Φ (m - 1)) hφ ν B
        ρ tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl
        (Vc n) (Vn n) (fun s x a₀ => fluxApprox n (fun v => Fc v s) x a₀) t
        (x + latticeShift l) a₀ v : PiLp 2 (fun _ : Fin 2 => h v)) =
      WithLp.toLp 2 fun a₀ => reconResFlux α q Λ m (Φ (m - 1)) hφ ν B
        ρ tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl
        (Vc n) (Vn n) (fun s x a₀ => fluxApprox n (fun v => Fc v s) x a₀) t x a₀ v
    congr 1
    funext a₀
    exact congrFun (hP a₀ l x) v

/-- Carriers of equal fields are equal. -/
theorem periodicHk_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] (K : ℕ) {f g : Vec 2 → E}
    (hfg : f = g) (hf : ContDiff ℝ (K : ℕ∞) f) (hfp : AVenhance.IsZ2Periodic f)
    (hg : ContDiff ℝ (K : ℕ∞) g) (hgp : AVenhance.IsZ2Periodic g) :
    periodicHk K f hf hfp = periodicHk K g hg hgp := by
  subst hfg
  rfl

/-- The truncated gradient factorial norm is nonnegative. -/
theorem gradFactorialNormSqUpTo_nonneg' {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {μ : Measure (Vec 2)} {K : ℕ} (ρ : ℝ) (m : ℕ) (X : JetL2 μ K E) :
    0 ≤ gradFactorialNormSqUpTo ρ m X := by
  unfold gradFactorialNormSqUpTo
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · exact mul_nonneg (factorialWeight_nonneg _ _) (derivativeNormSq_nonneg _ _)
  · exact le_rfl

/-- The combination of the slice bounds of the residual flux, with the densities kept separate. -/
theorem ennreal_slice_combine_sep (r : ℕ) {A X B' C' Y g f : ℝ} (hA : 0 ≤ A) (hX : 0 ≤ X)
    (hB : 0 ≤ B') (hC : 0 ≤ C') (hY : 0 ≤ Y) (hg : 0 ≤ g) (hf : 0 ≤ f) {gd fd : ℝ≥0∞}
    (hgd : gd ≤ ENNReal.ofReal g) (hfd : fd ≤ ENNReal.ofReal f) :
    2 ^ (r + 1) * (3 * (ENNReal.ofReal A * ENNReal.ofReal X * gd + ENNReal.ofReal B' * fd +
        ENNReal.ofReal C' * ENNReal.ofReal Y * fd)) ≤
      ENNReal.ofReal (2 ^ (r + 1) * (3 * (A * X * g + (B' + C' * Y) * f))) := by
  have h1 : 2 ^ (r + 1) * (3 * (ENNReal.ofReal A * ENNReal.ofReal X * gd + ENNReal.ofReal B' * fd +
      ENNReal.ofReal C' * ENNReal.ofReal Y * fd)) ≤
      2 ^ (r + 1) * (3 * (ENNReal.ofReal A * ENNReal.ofReal X * ENNReal.ofReal g +
        ENNReal.ofReal B' * ENNReal.ofReal f + ENNReal.ofReal C' * ENNReal.ofReal Y *
          ENNReal.ofReal f)) := by
    gcongr
  have e0 : 2 ^ (r + 1) * (3 * (A * X * g + (B' + C' * Y) * f)) =
      2 ^ (r + 1) * (3 * (A * X * g + B' * f + C' * Y * f)) := by ring
  have e : ENNReal.ofReal (2 ^ (r + 1) * (3 * (A * X * g + B' * f + C' * Y * f))) =
      2 ^ (r + 1) * (3 * (ENNReal.ofReal A * ENNReal.ofReal X * ENNReal.ofReal g +
        ENNReal.ofReal B' * ENNReal.ofReal f + ENNReal.ofReal C' * ENNReal.ofReal Y *
          ENNReal.ofReal f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (r + 1)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
      ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ A * X * g + B' * f)
        (by positivity : (0 : ℝ) ≤ C' * Y * f),
      ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ A * X * g) (by positivity : (0 : ℝ) ≤ B' * f),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ A * X), ENNReal.ofReal_mul hA,
      ENNReal.ofReal_mul hB, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C' * Y),
      ENNReal.ofReal_mul hC, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [e0, e]
  exact h1

/-- **The uniform bound of the residual flux carriers of the approximants**, with the densities of
the retained field and of the flux kept separate. -/
theorem ReconWindowAt.approxFlux_carrier_mass_le_sep
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
    (hkres : kres ≤ kc) (hmr : m' + 1 ≤ r₀) (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m)
    (hrsρ : rs ≤ ρ) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) :
    massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := Kc) rs π
        (fun v => (carrierOf (Kc v) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v t x)).val) ≤
      2 ^ (r + 1) * (3 * (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ) * (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) *
        (∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
            (W v t).val) +
        (((r.factorial : ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)) *
        massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v t).val))) := by
  have hπ := w.hcs.mass_pos
  obtain ⟨hs, hp⟩ := w.approxFlux_smooth hAcl hK hrL hord Vc Vn hch n ht Kc hKr
  have e : (fun v => (carrierOf (Kc v) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v t x)).val) = fun v =>
      (periodicHk (Kc v) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v t x) (hs v) (hp v)).val :=
    funext fun v => by rw [carrierOf_eq (Kc v) (hs v) (hp v)]
  rw [e]
  have hm := w.resFlux_mass_le hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr (coarseTraj n W) (Vc n)
    (hch n).1 (fun s x a₀ => fluxApprox n (fun v => Fc v s) x a₀)
    (fun s' k' => (fluxApprox_contDiff n (fun v => Fc v s') k').of_le
      (by exact_mod_cast le_top)) (Vn n) (hch n).lift_div ht
    ((coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top)) (coarseTraj_periodic n W t)
    (fun k' => fluxApprox_periodic n (fun v => Fc v t) k') hrs hrse hrsρ Kc hKr hs hp
  have hg0 : 0 ≤ ∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
      (W v t).val := Finset.sum_nonneg fun v _ =>
    mul_nonneg (inv_nonneg.2 (hπ v).le) (gradFactorialNormSqUpTo_nonneg' _ _ _)
  have hf0 : 0 ≤ massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
      ρ π (fun v => (Fc v t).val) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (factorialNormSq_nonneg _ _)
  have hgd : ResidualTimeData.gradDensity π ρ m'
      (coarseTraj n W) t ≤ ENNReal.ofReal (∑ v, (π v)⁻¹ *
        gradFactorialNormSqUpTo ρ m' (W v t).val) := by
    refine (gradDensity_coarseTraj_le π _ hmr w.hr₀ n W aRep (w.hrep t ht)).trans ?_
    unfold ResidualTimeData.gradDensity
    rw [ENNReal.ofReal_sum_of_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (gradFactorialNormSqUpTo_nonneg' _ _ _)]
    refine Finset.sum_le_sum fun v _ => le_of_eq ?_
    rw [classicalGradFactorialSq_eq_of_rep (w.hrep t ht v) _ hmr,
      ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)]
  have hfd := fluxDensity_fluxApprox_le π hπ ρ hkres n Fc t
  have hcomb := ennreal_slice_combine_sep r (X := (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2)) (Y := ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2))
    (tailPhysConst_nonneg H Nc D Acl r m' (pulseChartD Nχ))
    (sq_nonneg _) (sq_nonneg ((r.factorial : ℝ)))
    (liftPhysConst_nonneg H Nc Acl r kres Nχ (pulseChartD Nχ)) (by positivity) hg0 hf0 hgd hfd
  have hmn : 0 ≤ 2 ^ (r + 1) * (3 * (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ) * (((ocEll q Λ m
      ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) *
        (∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
            (W v t).val) +
        (((r.factorial : ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)) *
        massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v t).val))) := by
    have := tailPhysConst_nonneg H Nc D Acl r m' (pulseChartD Nχ)
    have := liftPhysConst_nonneg H Nc Acl r kres Nχ (pulseChartD Nχ)
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hmn).1 (hm.trans hcomb)

/-- **The difference bound of the residual flux carriers of two approximants.** -/
theorem ReconWindowAt.approxFlux_carrier_sub_mass_le
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
    (hkres : kres ≤ kc) (hmr : m' + 1 ≤ r₀) (n n' : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc tp (tp + Tobs)) {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m)
    (hrsρ : rs ≤ ρ) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) :
    massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := Kc) rs π
        (fun v => (carrierOf (Kc v) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v t x) -
          carrierOf (Kc v) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') n' Fc v t x)).val) ≤
      2 ^ (r + 1) * (3 * (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ) * (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
          ((r.factorial : ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2))) *
        ((∑ v, (π v)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc + D)) *
            ‖galerkinProj n (W v t) - galerkinProj n' (W v t)‖ ^ 2)) +
          ∑ v, (π v)⁻¹ * (factorialWeightMax ρ kc *
            ‖galerkinProj n (Fc v t) - galerkinProj n' (Fc v t)‖ ^ 2)) := by
  have hπ := w.hcs.mass_pos
  obtain ⟨hs, hp⟩ := w.approxFlux_smooth hAcl hK hrL hord Vc Vn hch n ht Kc hKr
  obtain ⟨hs', hp'⟩ := w.approxFlux_smooth hAcl hK hrL hord Vc Vn hch n' ht Kc hKr
  have hVd := w.tail_chains_sub (by omega : 1 ≤ Acl + 2 + r) (by omega : 1 ≤ r + 1) (by omega)
    (by omega) (coarseTraj n W) (coarseTraj n' W) (coarseTraj_contDiff n W)
    (coarseTraj_contDiff n' W) (Vc n) (Vc n') (hch n).1 (hch n').1
  have hVnd := w.lift_chains_sub (by omega : 1 ≤ Acl + 2 + r)
    (by omega : 1 ≤ max (Llift + 1) (Llift + 2))
    (fun s' x a₀ => fluxApprox n (fun v => Fc v s') x a₀)
    (fun s' x a₀ => fluxApprox n' (fun v => Fc v s') x a₀)
    (fun s' k' => fluxApprox_contDiff n (fun v => Fc v s') k')
    (fun s' k' => fluxApprox_contDiff n' (fun v => Fc v s') k') (Vn n) (Vn n')
    (hch n).lift_div (hch n').lift_div
  have e : ∀ v, (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp
      (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v t x - approxFlux α q Λ m (Φ (m -
            1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') n' Fc v t x) = fun x =>
      (WithLp.toLp 2 (fun a₀ => reconResFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl
        (fun k hh j τ X z a => Vc n k hh j τ X z a - Vc n' k hh j τ X z a)
        (fun k hh n'' j τ X z a => Vn n k hh n'' j τ X z a - Vn n' k hh n'' j τ X z a)
        (fun s' x a₀ => fluxApprox n (fun v => Fc v s') x a₀ - fluxApprox n' (fun v => Fc v s') x
            a₀) t x a₀ v) : PiLp 2 (fun _ : Fin 2 => h v)) := fun v => by
    funext x
    rw [approxFlux_eq_reconResFlux, approxFlux_eq_reconResFlux, ← WithLp.toLp_sub]
    congr 1
    funext a₀
    rw [reconResFlux_sub]
    rfl
  have hsd : ∀ v, ContDiff ℝ (Kc v : ℕ∞) (fun x => (WithLp.toLp 2 (fun a₀ => reconResFlux
      α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs) (fun k => F.weight
          (pp k)) H Nc Acl (fun k hh j τ X z a => Vc n k hh j τ X z a - Vc n' k hh j τ X z a)
      (fun k hh n'' j τ X z a => Vn n k hh n'' j τ X z a - Vn n' k hh n'' j τ X z a)
      (fun s' x a₀ => fluxApprox n (fun v => Fc v s') x a₀ - fluxApprox n' (fun v => Fc v s') x a₀)
          t x a₀ v) : PiLp 2 (fun _ : Fin 2 => h v))) := fun v => by
    rw [← e v]
    exact (hs v).sub (hs' v)
  have hpd : ∀ v, IsZ2Periodic (fun x => (WithLp.toLp 2 (fun a₀ => reconResFlux
      α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs) (fun k => F.weight
          (pp k)) H Nc Acl (fun k hh j τ X z a => Vc n k hh j τ X z a - Vc n' k hh j τ X z a)
      (fun k hh n'' j τ X z a => Vn n k hh n'' j τ X z a - Vn n' k hh n'' j τ X z a)
      (fun s' x a₀ => fluxApprox n (fun v => Fc v s') x a₀ - fluxApprox n' (fun v => Fc v s') x a₀)
          t x a₀ v) : PiLp 2 (fun _ : Fin 2 => h v))) := fun v => by
    rw [← e v]
    intro l x
    show approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v t (x + latticeShift l) -
        approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') n' Fc v t (x + latticeShift l) =
            approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v t x - approxFlux α q Λ m (Φ (m -
            1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') n' Fc v t x
    exact congrArg₂ (· - ·) (hp v l x) (hp' v l x)
  have ec : (fun v => (carrierOf (Kc v) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) n Fc v t x) -
      carrierOf (Kc v) (fun x => approxFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
        (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') n' Fc v t x)).val) = fun v =>
      (periodicHk (Kc v) _ (hsd v) (hpd v)).val := by
    funext v
    rw [carrierOf_eq (Kc v) (hs v) (hp v), carrierOf_eq (Kc v) (hs' v) (hp' v),
      periodicHk_sub (Kc v) (hs v) (hs' v) (hp v) (hp' v)]
    exact congrArg Subtype.val (periodicHk_congr (Kc v) (e v) _ _ (hsd v) (hpd v))
  simp only [ec]
  have hm := w.resFlux_mass_le hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr
    (fun s' x => coarseTraj n W s' x - coarseTraj n' W s' x)
    (fun k hh j τ X z a => Vc n k hh j τ X z a - Vc n' k hh j τ X z a) hVd
    (fun s' x a₀ => fluxApprox n (fun v => Fc v s') x a₀ - fluxApprox n' (fun v => Fc v s') x a₀)
    (fun s' k' => ((fluxApprox_contDiff n (fun v => Fc v s') k').sub
      (fluxApprox_contDiff n' (fun v => Fc v s') k')).of_le (by exact_mod_cast le_top))
    (fun k hh n'' j τ X z a => Vn n k hh n'' j τ X z a - Vn n' k hh n'' j τ X z a) hVnd ht
    (((coarseTraj_contDiff n W t).sub (coarseTraj_contDiff n' W t)).of_le
      (by exact_mod_cast le_top))
    (fun l x => by
      show coarseTraj n W t (x + latticeShift l) - coarseTraj n' W t (x + latticeShift l) =
        coarseTraj n W t x - coarseTraj n' W t x
      exact congrArg₂ (· - ·) (coarseTraj_periodic n W t l x) (coarseTraj_periodic n' W t l x))
    (fun k' l x => by
      show fluxApprox n (fun v => Fc v t) (x + latticeShift l) k' -
          fluxApprox n' (fun v => Fc v t) (x + latticeShift l) k' =
        fluxApprox n (fun v => Fc v t) x k' - fluxApprox n' (fun v => Fc v t) x k'
      exact congrArg₂ (· - ·) (fluxApprox_periodic n (fun v => Fc v t) k' l x)
        (fluxApprox_periodic n' (fun v => Fc v t) k' l x))
    hrs hrse hrsρ Kc hKr hsd hpd
  have hconv : ∀ a : ι → ℝ, (∀ v, 0 ≤ a v) →
      ∑ v, ENNReal.ofReal (π v)⁻¹ * ENNReal.ofReal (a v) =
        ENNReal.ofReal (∑ v, (π v)⁻¹ * a v) := fun a ha => by
    rw [ENNReal.ofReal_sum_of_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le) (ha v)]
    exact Finset.sum_congr rfl fun v _ => (ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)).symm
  have hwW : 0 ≤ factorialWeightMax ρ (kc + 1 + (Nc + D)) :=
    (factorialWeight_nonneg _ 0).trans (factorialWeight_le_max _ (0 : Fin (kc + 1 + (Nc + D) + 1)))
  have hwF : 0 ≤ factorialWeightMax ρ kc :=
    (factorialWeight_nonneg _ 0).trans (factorialWeight_le_max _ (0 : Fin (kc + 1)))
  have hgd := (gradDensity_coarseTraj_sub_le π ρ hmr w.hr₀ n n' W
      t).trans
    (le_of_eq (hconv _ fun v => mul_nonneg hwW (sq_nonneg _)))
  have hfd := (fluxDensity_fluxApprox_sub_le π ρ hkres n n' Fc
      t).trans
    (le_of_eq (hconv _ fun v => mul_nonneg hwF (sq_nonneg _)))
  have hg0 : 0 ≤ ∑ v, (π v)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc
      + D)) *
      ‖galerkinProj n (W v t) - galerkinProj n' (W v t)‖ ^ 2) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (mul_nonneg hwW (sq_nonneg _))
  have hf0 : 0 ≤ ∑ v, (π v)⁻¹ * (factorialWeightMax ρ kc *
      ‖galerkinProj n (Fc v t) - galerkinProj n' (Fc v t)‖ ^ 2) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (mul_nonneg hwF (sq_nonneg _))
  have hcomb := ennreal_slice_combine r (X := (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2)) (Y := ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2))
    (tailPhysConst_nonneg H Nc D Acl r m' (pulseChartD Nχ))
    (sq_nonneg _) (sq_nonneg ((r.factorial : ℝ)))
    (liftPhysConst_nonneg H Nc Acl r kres Nχ (pulseChartD Nχ)) (by positivity) hg0 hf0 hgd hfd
  have hmn : 0 ≤ 2 ^ (r + 1) * (3 * (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ) * (((ocEll q Λ m
      ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
      ((r.factorial : ℝ)) ^ 2 + liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ) * ((ocEpsilon q Λ
          m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2))) *
      ((∑ v, (π v)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc + D)) *
          ‖galerkinProj n (W v t) - galerkinProj n' (W v t)‖ ^ 2)) +
        ∑ v, (π v)⁻¹ * (factorialWeightMax ρ kc *
          ‖galerkinProj n (Fc v t) - galerkinProj n' (Fc v t)‖ ^ 2)) := by
    have := tailPhysConst_nonneg H Nc D Acl r m' (pulseChartD Nχ)
    have := liftPhysConst_nonneg H Nc Acl r kres Nχ (pulseChartD Nχ)
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hmn).1 (hm.trans hcomb)
end

/-! **The glued residual force of the Galerkin approximants**. The glued residual
force (the cleanup forces of the tails and of the lifted coarse flux) is linear in the cleanup
chains whose last members are slowly differentiable (`reconResForce_sub'`); the members of the
chains of a reconstruction window are (`ReconWindowAt.tail_chain_differentiable`,
`ReconWindowAt.lift_chain_differentiable`). At every time of the window, the glued residual force of
the `n`-th approximant is of class `C^{K_v}` and periodic (`ReconWindowAt.approxResForce_smooth`),
the mass-weighted norm of its carrier is bounded uniformly in `n` by the gradient density of the
retained field and the norm of the flux (`ReconWindowAt.approxResForce_carrier_mass_le`), and the
carriers of two approximants differ by at most the Galerkin differences of the retained field and
of the flux (`ReconWindowAt.approxResForce_carrier_sub_mass_le`). -/

section
section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The components of a box-smooth field are slowly differentiable. -/
theorem IsBoxSmooth.differentiable_component {sX sZ : ℕ} (hX : 1 ≤ sX)
    {V : Vec 2 → Vec 2 → Fin 2 → E} (hV : IsBoxSmooth sX sZ V) (z : Vec 2) (a : Fin 2) :
    Differentiable ℝ (fun X => V X z a) := by
  have hsX : ((sX : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : sX ≠ 0)
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) a).differentiable.comp
    ((hV.isSlowSmooth.1 z).differentiable hsX)

/-- The glued tail force of a difference of chains whose last members are slowly differentiable
at the weighted pulses. -/
theorem gluedTailForce_sub_chain (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ)
    (ψs : ℤ → ℝ → Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vc Vc' : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ)
    (hVc : ∀ k ∈ kset, ϖ k t ≠ 0 → ∀ hh, hh ≤ H → ∀ z a,
      Differentiable ℝ (fun X => Vc k hh (Acl - 1) (c⁻¹ * t) X z a))
    (hVc' : ∀ k ∈ kset, ϖ k t ≠ 0 → ∀ hh, hh ≤ H → ∀ z a,
      Differentiable ℝ (fun X => Vc' k hh (Acl - 1) (c⁻¹ * t) X z a)) (x : Vec 2) :
    gluedTailForce kset ϖ ψs H N Acl ε c ρs es
        (fun k hh j τ X z a => Vc k hh j τ X z a - Vc' k hh j τ X z a) t x =
      gluedTailForce kset ϖ ψs H N Acl ε c ρs es Vc t x -
        gluedTailForce kset ϖ ψs H N Acl ε c ρs es Vc' t x := by
  simp only [gluedTailForce, ← Finset.sum_sub_distrib, ← smul_sub]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hw : ϖ k t = 0
  · simp only [hw, zero_smul]
  · rw [tailForcePhys_sub_chain (ψs k t) H N Acl ε c ρs es (Vc k) (Vc' k) t (hVc k hk hw)
      (hVc' k hk hw)]

/-- The glued lifted force of a difference of chains whose last members are slowly
differentiable at the weighted pulses. -/
theorem gluedLiftForce_sub_chain (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ)
    (ψs : ℤ → ℝ → Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vn Vn' : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ)
    (hVn : ∀ k ∈ kset, ϖ k t ≠ 0 → ∀ hh, hh ≤ H → ∀ n, n < N → ∀ z a,
      Differentiable ℝ (fun X => Vn k hh n (Acl - 1) (c⁻¹ * t) X z a))
    (hVn' : ∀ k ∈ kset, ϖ k t ≠ 0 → ∀ hh, hh ≤ H → ∀ n, n < N → ∀ z a,
      Differentiable ℝ (fun X => Vn' k hh n (Acl - 1) (c⁻¹ * t) X z a)) (x : Vec 2) :
    gluedLiftForce kset ϖ ψs H N Acl ε c ρs es
        (fun k hh n j τ X z a => Vn k hh n j τ X z a - Vn' k hh n j τ X z a) t x =
      gluedLiftForce kset ϖ ψs H N Acl ε c ρs es Vn t x -
        gluedLiftForce kset ϖ ψs H N Acl ε c ρs es Vn' t x := by
  simp only [gluedLiftForce, ← Finset.sum_sub_distrib, ← smul_sub]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hw : ϖ k t = 0
  · simp only [hw, zero_smul]
  · rw [liftForcePhys_sub_chain (ψs k t) H N Acl ε c ρs es (Vn k) (Vn' k) t (hVn k hk hw)
      (hVn' k hk hw)]

end Linear

/-- The combination of the slice bounds of the residual force. -/
theorem ennreal_force_combine (r : ℕ) {A X B' Y g f : ℝ} (hA : 0 ≤ A) (hX : 0 ≤ X)
    (hB : 0 ≤ B') (hY : 0 ≤ Y) (hg : 0 ≤ g) (hf : 0 ≤ f) {gd fd : ℝ≥0∞}
    (hgd : gd ≤ ENNReal.ofReal g) (hfd : fd ≤ ENNReal.ofReal f) :
    2 ^ (r + 1) * (2 * (ENNReal.ofReal A * ENNReal.ofReal X * gd +
        ENNReal.ofReal B' * ENNReal.ofReal Y * fd)) ≤
      ENNReal.ofReal (2 ^ (r + 1) * (2 * (A * X + B' * Y)) * (g + f)) := by
  have h1 : 2 ^ (r + 1) * (2 * (ENNReal.ofReal A * ENNReal.ofReal X * gd +
      ENNReal.ofReal B' * ENNReal.ofReal Y * fd)) ≤
      2 ^ (r + 1) * (2 * (ENNReal.ofReal A * ENNReal.ofReal X * ENNReal.ofReal g +
        ENNReal.ofReal B' * ENNReal.ofReal Y * ENNReal.ofReal f)) := by
    gcongr
  have e : ENNReal.ofReal (2 ^ (r + 1) * (2 * (A * X * g + B' * Y * f))) =
      2 ^ (r + 1) * (2 * (ENNReal.ofReal A * ENNReal.ofReal X * ENNReal.ofReal g +
        ENNReal.ofReal B' * ENNReal.ofReal Y * ENNReal.ofReal f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (r + 1)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ A * X * g)
        (by positivity : (0 : ℝ) ≤ B' * Y * f),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ A * X), ENNReal.ofReal_mul hA,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ B' * Y), ENNReal.ofReal_mul hB,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  refine h1.trans (e ▸ ENNReal.ofReal_le_ofReal ?_)
  have h2 : 0 ≤ A * X := mul_nonneg hA hX
  have h3 : 0 ≤ B' * Y := mul_nonneg hB hY
  have h4 : (0 : ℝ) < 2 ^ (r + 1) := by positivity
  have h5 : A * X * g + B' * Y * f ≤ (A * X + B' * Y) * (g + f) := by
    have := mul_nonneg h2 hf
    have := mul_nonneg h3 hg
    have e' : (A * X + B' * Y) * (g + f) = A * X * g + B' * Y * f + (A * X * f + B' * Y * g) := by
      ring
    rw [e']
    exact le_add_of_nonneg_right (add_nonneg (mul_nonneg h2 hf) (mul_nonneg h3 hg))
  calc 2 ^ (r + 1) * (2 * (A * X * g + B' * Y * f))
      ≤ 2 ^ (r + 1) * (2 * ((A * X + B' * Y) * (g + f))) := by gcongr
    _ = 2 ^ (r + 1) * (2 * (A * X + B' * Y)) * (g + f) := by ring

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

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **The glued residual force of differences of chains is the difference of the glued residual
forces**, when the last members of the chains are slowly differentiable at the weighted pulses. -/
theorem reconResForce_sub' (α q : ℝ) (Λ m : ℕ) (φs : ℝ → Vec 2 → ℝ)
    (hφs : IsAdmissibleStream φs) (ν B ρ tA tZ : ℝ) (ϖ : ℤ → ℝ → ℝ) (H N Acl : ℕ)
    (Vc Vc' : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn Vn' : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) (t : ℝ)
    (hVc : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t ≠ 0 → ∀ hh, hh ≤ H → ∀ z a,
      Differentiable ℝ (fun X => Vc k hh (Acl - 1) ((ocEll q Λ m ν ^ 2)⁻¹ * t) X z a))
    (hVc' : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t ≠ 0 → ∀ hh, hh ≤ H → ∀ z a,
      Differentiable ℝ (fun X => Vc' k hh (Acl - 1) ((ocEll q Λ m ν ^ 2)⁻¹ * t) X z a))
    (hVn : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t ≠ 0 → ∀ hh, hh ≤ H → ∀ n, n < N → ∀ z a,
      Differentiable ℝ (fun X => Vn k hh n (Acl - 1) ((ocEll q Λ m ν ^ 2)⁻¹ * t) X z a))
    (hVn' : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ϖ k t ≠ 0 → ∀ hh, hh ≤ H → ∀ n, n < N → ∀ z a,
      Differentiable ℝ (fun X => Vn' k hh n (Acl - 1) ((ocEll q Λ m ν ^ 2)⁻¹ * t) X z a))
    (x : Vec 2) :
    reconResForce α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl
        (fun k hh j τ X z a => Vc k hh j τ X z a - Vc' k hh j τ X z a)
        (fun k hh n j τ X z a => Vn k hh n j τ X z a - Vn' k hh n j τ X z a) t x =
      reconResForce α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl Vc Vn t x -
        reconResForce α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl Vc' Vn' t x := by
  simp only [reconResForce]
  rw [gluedTailForce_sub_chain _ _ _ _ _ _ _ _ _ _ Vc Vc' t hVc hVc',
    gluedLiftForce_sub_chain _ _ _ _ _ _ _ _ _ _ Vn Vn' t hVn hVn']
  abel

/-- **The members of the tail chains of a smooth field are slowly differentiable.** -/
theorem ReconWindowAt.tail_chain_differentiable
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {sXc sZc Acl : ℕ} (hXc : 1 ≤ sXc) (hX : sXc ≤ Klift + D + 2)
    (hZ : sZc ≤ max (Llift + 1) (Llift + 2)) (u : ℝ → Vec 2 → ∀ i, h i)
    (hu : ∀ s', ContDiff ℝ (⊤ : ℕ∞) (u s'))
    (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H →
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
        (fun j => Vc k hh j τ)) :
    ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2), ∀ j, j < Acl →
            ∀ z a,
        Differentiable ℝ (fun X => Vc k hh j τ X z a) := by
  intro k hk hh hhh τ hτ j hj z a
  have P := w.hsetting k hk
  have hseq := w.hseq k hk
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun X : Vec 2 => ocChart α q Λ m (Φ (m - 1)) hφ
      (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * τ)
        (ρ • X)) :=
    (contDiff_ocChart hφ α q Λ m _ _).comp (contDiff_const_smul _)
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun X => u (ocEll q Λ m ν ^ 2 * τ) (ocChart α q Λ m (Φ (m - 1))
      hφ (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * τ) (ρ •
          X))) :=
    (hu _).comp hχ
  have hpres := fun (n : ℕ) (hn1 : Nc + 1 ≤ n) (hn2 : n ≤ 2 * Nc + D) =>
    setting_tail_presentation P (Klift + D + 2) (max (Llift + 1) (Llift + 2)) (by omega)
      (by omega) (Cc k) hseq hh hhh n (by omega) hn2
  have hF := (isBoxSmooth_tailFluxField_of_presentation (f := fun _ => 0)
    (F := fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
      ρ (ρ / ocEpsilon q Λ (m - 1))
      k (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) hpres
    (ocDStar q Λ m ν B / ρ)
    (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
      (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s') (ρ • X)))
          hτ hA).mono hX hZ
  exact IsBoxSmooth.differentiable_component hXc
    (IsCleanupChain.isBoxSmooth hF (hV k hk hh hhh τ hτ) j hj) z a

/-- **The members of the lift chains are slowly differentiable.** -/
theorem ReconWindowAt.lift_chain_differentiable
    (_w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {sXl sZl Acl : ℕ} (hXl : 1 ≤ sXl) (G : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXl sZl Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
          fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k')
            (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
              (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k'))
          τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n' j τ)) :
    ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2), ∀ j, j < Acl →
            ∀ z a,
        Differentiable ℝ (fun X => Vn k hh n' j τ X z a) :=
  fun k hk hh hhh n' hn' τ hτ j hj z a =>
    IsBoxSmooth.differentiable_component hXl
      (IsCleanupChain.isBoxSmooth (isBoxSmooth_zero sXl sZl) (hV k hk hh hhh n' hn' τ hτ) j hj) z a

/-- **The glued residual force of the difference of two approximants** is the difference of the
glued residual forces. -/
theorem ReconWindowAt.approxResForce_sub
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift) (hrL : r ≤ Llift)
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (n n' : ℕ) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (x : Vec 2) :
    reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl
        (fun k hh j τ X z a => Vc n k hh j τ X z a - Vc n' k hh j τ X z a)
        (fun k hh n'' j τ X z a => Vn n k hh n'' j τ X z a - Vn n' k hh n'' j τ X z a) t x =
      reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x -
        reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') t x := by
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hcell : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), F.weight (pp k) t ≠ 0 →
      (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    fun k hk hw => AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0
      (w.hpart.2.2.2.1 k hk t hw) ht
  have hT := fun (n₀ : ℕ) => w.tail_chain_differentiable (by omega : 1 ≤ Acl + 2 + r)
    (by omega : Acl + 2 + r ≤ Klift + D + 2) (by omega : r + 1 ≤ max (Llift + 1) (Llift + 2))
    (coarseTraj n₀ W) (coarseTraj_contDiff n₀ W) (Vc n₀) (hch n₀).1
  have hL := fun (n₀ : ℕ) => w.lift_chain_differentiable (by omega : 1 ≤ Acl + 2 + r)
    (fun s' x a₀ => fluxApprox n₀ (fun v => Fc v s') x a₀) (Vn n₀) (hch n₀).lift_div
  exact reconResForce_sub' α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp +
      Tobs)
    (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vc n') (Vn n) (Vn n') t
    (fun k hk hw hh hhh z a => hT n k hk hh hhh _ (hcell k hk hw) (Acl - 1) (by omega) z a)
    (fun k hk hw hh hhh z a => hT n' k hk hh hhh _ (hcell k hk hw) (Acl - 1) (by omega) z a)
    (fun k hk hw hh hhh n'' hn'' z a => hL n k hk hh hhh n'' hn'' _ (hcell k hk hw) (Acl - 1)
      (by omega) z a)
    (fun k hk hw hh hhh n'' hn'' z a => hL n' k hk hh hhh n'' hn'' _ (hcell k hk hw) (Acl - 1)
      (by omega) z a) x

/-- **The glued residual force of an approximant is smooth and periodic** at a time of the
window. -/
theorem ReconWindowAt.approxResForce_smooth
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r m' : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) :
    (∀ v, ContDiff ℝ (Kc v : ℕ∞) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v)) ∧
    (∀ v, IsZ2Periodic (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v)) := by
  have hT := (w.glued_tail_contDiff hAcl hK hrL hord (coarseTraj n W) (Vc n) (hch n).1 ht
    ((coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top))).2
  have hL := (w.glued_lift_contDiff hAcl hrL (fun s x a₀ => fluxApprox n (fun v => Fc v s) x a₀)
    (Vn n) (hch n).lift_div ht).2
  have hP := (w.res_periodic hAcl (by omega : 1 ≤ r + 1)
    (by omega : 1 ≤ max (Llift + 1) (Llift + 2)) (coarseTraj n W) (Vc n) (hch n).1
    (fun s x a₀ => fluxApprox n (fun v => Fc v s) x a₀) (Vn n) (hch n).lift_div ht
    (coarseTraj_periodic n W t) (fun k' => fluxApprox_periodic n (fun v => Fc v t) k')).2
  have hq : ContDiff ℝ (r : ℕ∞) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x) := hT.add hL
  exact ⟨fun v => (contDiff_pi.1 hq v).of_le (by exact_mod_cast hKr v),
    fun v l x => congrFun (hP l x) v⟩

/-- **The uniform bound of the glued residual force carriers of the approximants.** -/
theorem ReconWindowAt.approxResForce_carrier_mass_le
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
    (hkres : kres ≤ kc) (hmr : m' + 1 ≤ r₀) (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) :
    massNormSq (E := h) (K := Kc) rs π
        (fun v => (carrierOf (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v)).val) ≤
      (2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m' (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) *
        ((∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
            (W v t).val) +
          massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v t).val)) := by
  have hπ := w.hcs.mass_pos
  obtain ⟨hs, hp⟩ := w.approxResForce_smooth hAcl hK hrL hord Vc Vn hch n ht Kc hKr
  have e : (fun v => (carrierOf (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v)).val) = fun v =>
      (periodicHk (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v) (hs v) (hp v)).val
            :=
    funext fun v => by rw [carrierOf_eq (Kc v) (hs v) (hp v)]
  rw [e]
  have hm := w.resForce_mass_le hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr (coarseTraj n W) (Vc n)
    (hch n).1 (fun s x a₀ => fluxApprox n (fun v => Fc v s) x a₀)
    (fun s' k' => (fluxApprox_contDiff n (fun v => Fc v s') k').of_le
      (by exact_mod_cast le_top)) (Vn n) (hch n).lift_div ht
    ((coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top)) (coarseTraj_periodic n W t)
    (fun k' => fluxApprox_periodic n (fun v => Fc v t) k') hrs hrse Kc hKr hs hp
  have hg0 : 0 ≤ ∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
      (W v t).val := Finset.sum_nonneg fun v _ =>
    mul_nonneg (inv_nonneg.2 (hπ v).le) (gradFactorialNormSqUpTo_nonneg' _ _ _)
  have hf0 : 0 ≤ massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
      ρ π (fun v => (Fc v t).val) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (factorialNormSq_nonneg _ _)
  have hgd : ResidualTimeData.gradDensity π ρ m'
      (coarseTraj n W) t ≤ ENNReal.ofReal (∑ v, (π v)⁻¹ *
        gradFactorialNormSqUpTo ρ m' (W v t).val) := by
    refine (gradDensity_coarseTraj_le π _ hmr w.hr₀ n W aRep (w.hrep t ht)).trans ?_
    unfold ResidualTimeData.gradDensity
    rw [ENNReal.ofReal_sum_of_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (gradFactorialNormSqUpTo_nonneg' _ _ _)]
    refine Finset.sum_le_sum fun v _ => le_of_eq ?_
    rw [classicalGradFactorialSq_eq_of_rep (w.hrep t ht v) _ hmr,
      ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)]
  have hfd := fluxDensity_fluxApprox_le π hπ ρ hkres n Fc t
  have hcomb := ennreal_force_combine r (X := (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2)) (Y :=
              ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2))
    (tailForceConst_nonneg H Nc D Acl r m' (pulseChartD Nχ)) (sq_nonneg _)
    (liftForceConst_nonneg H Nc Acl r kres Nχ (pulseChartD Nχ)) (by positivity) hg0 hf0 hgd hfd
  have hmn : 0 ≤ (2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m' (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) *
        ((∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
            (W v t).val) +
          massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v t).val)) := by
    have := tailForceConst_nonneg H Nc D Acl r m' (pulseChartD Nχ)
    have := liftForceConst_nonneg H Nc Acl r kres Nχ (pulseChartD Nχ)
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hmn).1 (hm.trans hcomb)

/-- The combination of the slice bounds of the residual force, with the densities kept
separate. -/
theorem ennreal_force_combine_sep (r : ℕ) {A X B' Y g f : ℝ} (hA : 0 ≤ A) (hX : 0 ≤ X)
    (hB : 0 ≤ B') (hY : 0 ≤ Y) (hg : 0 ≤ g) (hf : 0 ≤ f) {gd fd : ℝ≥0∞}
    (hgd : gd ≤ ENNReal.ofReal g) (hfd : fd ≤ ENNReal.ofReal f) :
    2 ^ (r + 1) * (2 * (ENNReal.ofReal A * ENNReal.ofReal X * gd +
        ENNReal.ofReal B' * ENNReal.ofReal Y * fd)) ≤
      ENNReal.ofReal (2 ^ (r + 1) * (2 * (A * X * g + B' * Y * f))) := by
  have h1 : 2 ^ (r + 1) * (2 * (ENNReal.ofReal A * ENNReal.ofReal X * gd +
      ENNReal.ofReal B' * ENNReal.ofReal Y * fd)) ≤
      2 ^ (r + 1) * (2 * (ENNReal.ofReal A * ENNReal.ofReal X * ENNReal.ofReal g +
        ENNReal.ofReal B' * ENNReal.ofReal Y * ENNReal.ofReal f)) := by
    gcongr
  have e : ENNReal.ofReal (2 ^ (r + 1) * (2 * (A * X * g + B' * Y * f))) =
      2 ^ (r + 1) * (2 * (ENNReal.ofReal A * ENNReal.ofReal X * ENNReal.ofReal g +
        ENNReal.ofReal B' * ENNReal.ofReal Y * ENNReal.ofReal f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (r + 1)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ A * X * g)
        (by positivity : (0 : ℝ) ≤ B' * Y * f),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ A * X), ENNReal.ofReal_mul hA,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ B' * Y), ENNReal.ofReal_mul hB,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [e]
  exact h1

/-- **The uniform bound of the glued residual force carriers of the approximants**, with the
densities of the retained field and of the flux kept separate. -/
theorem ReconWindowAt.approxResForce_carrier_mass_le_sep
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
    (hkres : kres ≤ kc) (hmr : m' + 1 ≤ r₀) (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) :
    massNormSq (E := h) (K := Kc) rs π
        (fun v => (carrierOf (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v)).val) ≤
      2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m' (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) * (∑ v,
              (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
            (W v t).val) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2) * massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h
              v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v t).val))) := by
  have hπ := w.hcs.mass_pos
  obtain ⟨hs, hp⟩ := w.approxResForce_smooth hAcl hK hrL hord Vc Vn hch n ht Kc hKr
  have e : (fun v => (carrierOf (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v)).val) = fun v =>
      (periodicHk (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v) (hs v) (hp v)).val
            :=
    funext fun v => by rw [carrierOf_eq (Kc v) (hs v) (hp v)]
  rw [e]
  have hm := w.resForce_mass_le hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr (coarseTraj n W) (Vc n)
    (hch n).1 (fun s x a₀ => fluxApprox n (fun v => Fc v s) x a₀)
    (fun s' k' => (fluxApprox_contDiff n (fun v => Fc v s') k').of_le
      (by exact_mod_cast le_top)) (Vn n) (hch n).lift_div ht
    ((coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top)) (coarseTraj_periodic n W t)
    (fun k' => fluxApprox_periodic n (fun v => Fc v t) k') hrs hrse Kc hKr hs hp
  have hg0 : 0 ≤ ∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
      (W v t).val := Finset.sum_nonneg fun v _ =>
    mul_nonneg (inv_nonneg.2 (hπ v).le) (gradFactorialNormSqUpTo_nonneg' _ _ _)
  have hf0 : 0 ≤ massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
      ρ π (fun v => (Fc v t).val) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (factorialNormSq_nonneg _ _)
  have hgd : ResidualTimeData.gradDensity π ρ m'
      (coarseTraj n W) t ≤ ENNReal.ofReal (∑ v, (π v)⁻¹ *
        gradFactorialNormSqUpTo ρ m' (W v t).val) := by
    refine (gradDensity_coarseTraj_le π _ hmr w.hr₀ n W aRep (w.hrep t ht)).trans ?_
    unfold ResidualTimeData.gradDensity
    rw [ENNReal.ofReal_sum_of_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (gradFactorialNormSqUpTo_nonneg' _ _ _)]
    refine Finset.sum_le_sum fun v _ => le_of_eq ?_
    rw [classicalGradFactorialSq_eq_of_rep (w.hrep t ht v) _ hmr,
      ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)]
  have hfd := fluxDensity_fluxApprox_le π hπ ρ hkres n Fc t
  have hcomb := ennreal_force_combine_sep r (X := (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2)) (Y :=
              ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2))
    (tailForceConst_nonneg H Nc D Acl r m' (pulseChartD Nχ)) (sq_nonneg _)
    (liftForceConst_nonneg H Nc Acl r kres Nχ (pulseChartD Nχ)) (by positivity) hg0 hf0 hgd hfd
  have hmn : 0 ≤ 2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m' (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) * (∑ v,
              (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
            (W v t).val) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2) * massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h
              v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v t).val))) := by
    have := tailForceConst_nonneg H Nc D Acl r m' (pulseChartD Nχ)
    have := liftForceConst_nonneg H Nc Acl r kres Nχ (pulseChartD Nχ)
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hmn).1 (hm.trans hcomb)

/-- **The difference bound of the glued residual force carriers of two approximants.** -/
theorem ReconWindowAt.approxResForce_carrier_sub_mass_le
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
    (hkres : kres ≤ kc) (hmr : m' + 1 ≤ r₀) (n n' : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc tp (tp + Tobs)) {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m)
    (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) :
    massNormSq (E := h) (K := Kc) rs π
        (fun v => (carrierOf (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v) -
          carrierOf (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') t x v)).val) ≤
      (2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m' (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) *
        ((∑ v, (π v)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc + D)) *
            ‖galerkinProj n (W v t) - galerkinProj n' (W v t)‖ ^ 2)) +
          ∑ v, (π v)⁻¹ * (factorialWeightMax ρ kc *
            ‖galerkinProj n (Fc v t) - galerkinProj n' (Fc v t)‖ ^ 2)) := by
  have hπ := w.hcs.mass_pos
  obtain ⟨hs, hp⟩ := w.approxResForce_smooth hAcl hK hrL hord Vc Vn hch n ht Kc hKr
  obtain ⟨hs', hp'⟩ := w.approxResForce_smooth hAcl hK hrL hord Vc Vn hch n' ht Kc hKr
  have hVd := w.tail_chains_sub (by omega : 1 ≤ Acl + 2 + r) (by omega : 1 ≤ r + 1) (by omega)
    (by omega) (coarseTraj n W) (coarseTraj n' W) (coarseTraj_contDiff n W)
    (coarseTraj_contDiff n' W) (Vc n) (Vc n') (hch n).1 (hch n').1
  have hVnd := w.lift_chains_sub (by omega : 1 ≤ Acl + 2 + r)
    (by omega : 1 ≤ max (Llift + 1) (Llift + 2))
    (fun s' x a₀ => fluxApprox n (fun v => Fc v s') x a₀)
    (fun s' x a₀ => fluxApprox n' (fun v => Fc v s') x a₀)
    (fun s' k' => fluxApprox_contDiff n (fun v => Fc v s') k')
    (fun s' k' => fluxApprox_contDiff n' (fun v => Fc v s') k') (Vn n) (Vn n')
    (hch n).lift_div (hch n').lift_div
  have e : ∀ v, (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v - reconResForce α q Λ
            m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') t x v) = fun x =>
      reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl
        (fun k hh j τ X z a => Vc n k hh j τ X z a - Vc n' k hh j τ X z a)
        (fun k hh n'' j τ X z a => Vn n k hh n'' j τ X z a - Vn n' k hh n'' j τ X z a) t x v := fun
            v => by
    funext x
    rw [w.approxResForce_sub hAcl hK hrL Vc Vn hch n n' ht x]
    rfl
  have hsd : ∀ v, ContDiff ℝ (Kc v : ℕ∞) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B
      ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl
        (fun k hh j τ X z a => Vc n k hh j τ X z a - Vc n' k hh j τ X z a)
        (fun k hh n'' j τ X z a => Vn n k hh n'' j τ X z a - Vn n' k hh n'' j τ X z a) t x v) := fun
            v => by
    rw [← e v]
    exact (hs v).sub (hs' v)
  have hpd : ∀ v, IsZ2Periodic (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl
        (fun k hh j τ X z a => Vc n k hh j τ X z a - Vc n' k hh j τ X z a)
        (fun k hh n'' j τ X z a => Vn n k hh n'' j τ X z a - Vn n' k hh n'' j τ X z a) t x v) := fun
            v => by
    rw [← e v]
    intro l x
    exact congrArg₂ (· - ·) (hp v l x) (hp' v l x)
  have ec : (fun v => (carrierOf (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B
      ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v) -
      carrierOf (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') t x v)).val) = fun v =>
      (periodicHk (Kc v) _ (hsd v) (hpd v)).val := by
    funext v
    rw [carrierOf_eq (Kc v) (hs v) (hp v), carrierOf_eq (Kc v) (hs' v) (hp' v),
      periodicHk_sub (Kc v) (hs v) (hs' v) (hp v) (hp' v)]
    exact congrArg Subtype.val (periodicHk_congr (Kc v) (e v) _ _ (hsd v) (hpd v))
  simp only [ec]
  have hm := w.resForce_mass_le hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr
    (fun s' x => coarseTraj n W s' x - coarseTraj n' W s' x)
    (fun k hh j τ X z a => Vc n k hh j τ X z a - Vc n' k hh j τ X z a) hVd
    (fun s' x a₀ => fluxApprox n (fun v => Fc v s') x a₀ - fluxApprox n' (fun v => Fc v s') x a₀)
    (fun s' k' => ((fluxApprox_contDiff n (fun v => Fc v s') k').sub
      (fluxApprox_contDiff n' (fun v => Fc v s') k')).of_le (by exact_mod_cast le_top))
    (fun k hh n'' j τ X z a => Vn n k hh n'' j τ X z a - Vn n' k hh n'' j τ X z a) hVnd ht
    (((coarseTraj_contDiff n W t).sub (coarseTraj_contDiff n' W t)).of_le
      (by exact_mod_cast le_top))
    (fun l x => by
      show coarseTraj n W t (x + latticeShift l) - coarseTraj n' W t (x + latticeShift l) =
        coarseTraj n W t x - coarseTraj n' W t x
      exact congrArg₂ (· - ·) (coarseTraj_periodic n W t l x) (coarseTraj_periodic n' W t l x))
    (fun k' l x => by
      show fluxApprox n (fun v => Fc v t) (x + latticeShift l) k' -
          fluxApprox n' (fun v => Fc v t) (x + latticeShift l) k' =
        fluxApprox n (fun v => Fc v t) x k' - fluxApprox n' (fun v => Fc v t) x k'
      exact congrArg₂ (· - ·) (fluxApprox_periodic n (fun v => Fc v t) k' l x)
        (fluxApprox_periodic n' (fun v => Fc v t) k' l x))
    hrs hrse Kc hKr hsd hpd
  have hconv : ∀ a : ι → ℝ, (∀ v, 0 ≤ a v) →
      ∑ v, ENNReal.ofReal (π v)⁻¹ * ENNReal.ofReal (a v) =
        ENNReal.ofReal (∑ v, (π v)⁻¹ * a v) := fun a ha => by
    rw [ENNReal.ofReal_sum_of_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le) (ha v)]
    exact Finset.sum_congr rfl fun v _ => (ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)).symm
  have hwW : 0 ≤ factorialWeightMax ρ (kc + 1 + (Nc + D)) :=
    (factorialWeight_nonneg _ 0).trans (factorialWeight_le_max _ (0 : Fin (kc + 1 + (Nc + D) + 1)))
  have hwF : 0 ≤ factorialWeightMax ρ kc :=
    (factorialWeight_nonneg _ 0).trans (factorialWeight_le_max _ (0 : Fin (kc + 1)))
  have hgd := (gradDensity_coarseTraj_sub_le π ρ hmr w.hr₀ n n' W
      t).trans
    (le_of_eq (hconv _ fun v => mul_nonneg hwW (sq_nonneg _)))
  have hfd := (fluxDensity_fluxApprox_sub_le π ρ hkres n n' Fc
      t).trans
    (le_of_eq (hconv _ fun v => mul_nonneg hwF (sq_nonneg _)))
  have hg0 : 0 ≤ ∑ v, (π v)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc
      + D)) *
      ‖galerkinProj n (W v t) - galerkinProj n' (W v t)‖ ^ 2) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (mul_nonneg hwW (sq_nonneg _))
  have hf0 : 0 ≤ ∑ v, (π v)⁻¹ * (factorialWeightMax ρ kc *
      ‖galerkinProj n (Fc v t) - galerkinProj n' (Fc v t)‖ ^ 2) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (mul_nonneg hwF (sq_nonneg _))
  have hcomb := ennreal_force_combine r (X := (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2)) (Y :=
              ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2))
    (tailForceConst_nonneg H Nc D Acl r m' (pulseChartD Nχ)) (sq_nonneg _)
    (liftForceConst_nonneg H Nc Acl r kres Nχ (pulseChartD Nχ)) (by positivity) hg0 hf0 hgd hfd
  have hmn : 0 ≤ (2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m' (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) *
        ((∑ v, (π v)⁻¹ * (factorialWeightMax ρ (kc + 1 + (Nc + D)) *
            ‖galerkinProj n (W v t) - galerkinProj n' (W v t)‖ ^ 2)) +
          ∑ v, (π v)⁻¹ * (factorialWeightMax ρ kc *
            ‖galerkinProj n (Fc v t) - galerkinProj n' (Fc v t)‖ ^ 2)) := by
    have := tailForceConst_nonneg H Nc D Acl r m' (pulseChartD Nχ)
    have := liftForceConst_nonneg H Nc Acl r kres Nχ (pulseChartD Nχ)
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hmn).1 (hm.trans hcomb)
end

end AVRegularity.CycleComparison.Reconstruction
end
