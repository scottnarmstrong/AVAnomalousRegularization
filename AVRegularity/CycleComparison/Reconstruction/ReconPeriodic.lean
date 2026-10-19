-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.ReconLiftSlices
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.Lift.SettingConstructedLiftSequence
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The residual of a coarse field on a reconstruction window at one time**. For a coarse field `u` with tail chains `Vc` and a
flux field `G` with lift chains `Vn` of its divergence, the residual flux is the glued tail flux
plus `G` plus the glued lifted flux (`reconResFlux`), and the residual force is the glued tail
force plus the glued lifted force (`reconResForce`); for the Galerkin approximant
(`u = a_n`, `G = S_n F_c`) these are the residual `approxFlux` and the first two terms of
`approxForce` (`approxFlux_eq_reconResFlux`). At every time of the window:
* the glued pieces are of class `C^r` (`ReconWindowAt.glued_tail_contDiff`,
  `ReconWindowAt.glued_lift_contDiff`);
* every weighted word derivative of order `j ≤ r` of the residual flux is bounded by the
  gradient energy density of `u` and the jet density of `G` (`ReconWindowAt.resFlux_word_le`), and
  so is the residual force (`ReconWindowAt.resForce_word_le`). -/

section
section Defs

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The residual flux of a coarse field with tail chains `Vc` and a flux field `G` with lift
chains `Vn`, glued over the observed pulses. -/
def reconResFlux (α q : ℝ) (Λ m : ℕ) (φs : ℝ → Vec 2 → ℝ) (hφs : IsAdmissibleStream φs)
    (ν B ρ tA tZ : ℝ) (ϖ : ℤ → ℝ → ℝ) (H N Acl : ℕ)
    (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (G : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) (a₀ : Fin 2) : ∀ i, h i :=
  gluedTailFlux (ocObsPulses α q Λ m tA tZ) ϖ
      (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) H N Acl
      (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vc t x a₀
    + G t x a₀
    + gluedLiftFlux (ocObsPulses α q Λ m tA tZ) ϖ
      (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) H N Acl
      (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vn t x a₀

/-- The residual force of a coarse field with tail chains `Vc` and of a flux field with lift
chains `Vn`, glued over the observed pulses. -/
def reconResForce (α q : ℝ) (Λ m : ℕ) (φs : ℝ → Vec 2 → ℝ) (hφs : IsAdmissibleStream φs)
    (ν B ρ tA tZ : ℝ) (ϖ : ℤ → ℝ → ℝ) (H N Acl : ℕ)
    (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) :
    ∀ i, h i :=
  gluedTailForce (ocObsPulses α q Λ m tA tZ) ϖ
      (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) H N Acl
      (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vc t x
    + gluedLiftForce (ocObsPulses α q Λ m tA tZ) ϖ
      (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) H N Acl
      (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vn t x

end Defs

section Slices

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

omit [∀ i, NormedSpace ℝ (h i)] in
/-- The flux slice norm of a sum of three fluxes. -/
theorem fluxInt_add_three_le (A₁ A₂ A₃ : Vec 2 → Fin 2 → ∀ i, h i)
    (h₁ : ∀ k, Continuous (fun x => A₁ x k)) (h₂ : ∀ k, Continuous (fun x => A₂ x k))
    (h₃ : ∀ k, Continuous (fun x => A₃ x k)) (π : ι → ℝ) :
    fluxInt π (fun x k => A₁ x k + A₂ x k + A₃ x k) ≤
      3 * (fluxInt π A₁ + fluxInt π A₂ + fluxInt π A₃) := by
  have h := fluxInt_sum_le (Finset.univ : Finset (Fin 3)) ![A₁, A₂, A₃]
    (fun i _ k => by fin_cases i <;> simp [h₁, h₂, h₃]) π
  simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
  exact_mod_cast h

omit [∀ i, NormedSpace ℝ (h i)] in
/-- The scalar slice norm of a sum of two fields. -/
theorem scalInt_add_two_le (q₁ q₂ : Vec 2 → ∀ i, h i) (h₁ : Continuous q₁)
    (h₂ : Continuous q₂) (π : ι → ℝ) :
    scalInt π (fun x => q₁ x + q₂ x) ≤ 2 * (scalInt π q₁ + scalInt π q₂) := by
  have h := scalInt_sum_le (Finset.univ : Finset (Fin 2)) ![q₁, q₂]
    (fun i _ => by fin_cases i <;> simp [h₁, h₂]) π
  simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h
  exact_mod_cast h

/-- The weighted word derivatives of a sum of three fluxes. -/
theorem fluxInt_word_add_three_le (A₁ A₂ A₃ : Vec 2 → Fin 2 → ∀ i, h i) {j : ℕ}
    (h₁ : ∀ k, ContDiff ℝ (j : ℕ∞) (fun x => A₁ x k))
    (h₂ : ∀ k, ContDiff ℝ (j : ℕ∞) (fun x => A₂ x k))
    (h₃ : ∀ k, ContDiff ℝ (j : ℕ∞) (fun x => A₃ x k)) (rs : ℝ) (β : DerivativeWord2 j)
    (π : ι → ℝ) :
    fluxInt π (fun x a₀ => rs ^ j • orderedDerivative β
        (fun x' => A₁ x' a₀ + A₂ x' a₀ + A₃ x' a₀) x) ≤
      3 * (fluxInt π (fun x a₀ => rs ^ j • orderedDerivative β (fun x' => A₁ x' a₀) x) +
        fluxInt π (fun x a₀ => rs ^ j • orderedDerivative β (fun x' => A₂ x' a₀) x) +
        fluxInt π (fun x a₀ => rs ^ j • orderedDerivative β (fun x' => A₃ x' a₀) x)) := by
  have e : (fun x a₀ => rs ^ j • orderedDerivative β
      (fun x' => A₁ x' a₀ + A₂ x' a₀ + A₃ x' a₀) x) = fun x a₀ =>
      rs ^ j • orderedDerivative β (fun x' => A₁ x' a₀) x +
      rs ^ j • orderedDerivative β (fun x' => A₂ x' a₀) x +
      rs ^ j • orderedDerivative β (fun x' => A₃ x' a₀) x := by
    funext x a₀
    rw [orderedDerivative_add β ((h₁ a₀).add (h₂ a₀)) (h₃ a₀),
      orderedDerivative_add β (h₁ a₀) (h₂ a₀)]
    simp only [smul_add]
  refine (le_of_eq (congrArg (fluxInt π) e)).trans ?_
  exact fluxInt_add_three_le
    (fun x a₀ => rs ^ j • orderedDerivative β (fun x' => A₁ x' a₀) x)
    (fun x a₀ => rs ^ j • orderedDerivative β (fun x' => A₂ x' a₀) x)
    (fun x a₀ => rs ^ j • orderedDerivative β (fun x' => A₃ x' a₀) x)
    (fun k => (continuous_orderedDerivative β (h₁ k)).const_smul (rs ^ j))
    (fun k => (continuous_orderedDerivative β (h₂ k)).const_smul (rs ^ j))
    (fun k => (continuous_orderedDerivative β (h₃ k)).const_smul (rs ^ j)) π

/-- The weighted word derivatives of a sum of two fields. -/
theorem scalInt_word_add_two_le (q₁ q₂ : Vec 2 → ∀ i, h i) {j : ℕ}
    (h₁ : ContDiff ℝ (j : ℕ∞) q₁) (h₂ : ContDiff ℝ (j : ℕ∞) q₂) (rs : ℝ)
    (β : DerivativeWord2 j) (π : ι → ℝ) :
    scalInt π (fun x => rs ^ j • orderedDerivative β (fun x' => q₁ x' + q₂ x') x) ≤
      2 * (scalInt π (fun x => rs ^ j • orderedDerivative β q₁ x) +
        scalInt π (fun x => rs ^ j • orderedDerivative β q₂ x)) := by
  have e : (fun x => rs ^ j • orderedDerivative β (fun x' => q₁ x' + q₂ x') x) = fun x =>
      rs ^ j • orderedDerivative β q₁ x + rs ^ j • orderedDerivative β q₂ x := by
    funext x
    rw [orderedDerivative_add β h₁ h₂]
    simp only [smul_add]
  refine (le_of_eq (congrArg (scalInt π) e)).trans ?_
  exact scalInt_add_two_le (fun x => rs ^ j • orderedDerivative β q₁ x)
    (fun x => rs ^ j • orderedDerivative β q₂ x)
    ((continuous_orderedDerivative β h₁).const_smul (rs ^ j))
    ((continuous_orderedDerivative β h₂).const_smul (rs ^ j)) π

/-- **The identity term**: the weighted word derivatives of a flux field by its jet density. -/
theorem fluxInt_word_le_fluxDensity (π : ι → ℝ) {ρ rs : ℝ} (hrs : 0 < rs) (hρ : rs ≤ ρ)
    {j m : ℕ} (hjm : j ≤ m) (β : DerivativeWord2 j) (G : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (t : ℝ)
    (hG : ∀ k, ContDiff ℝ (j : ℕ∞) (fun x => G t x k)) :
    fluxInt π (fun x a₀ => rs ^ j • orderedDerivative β (fun x' => G t x' a₀) x) ≤
      ENNReal.ofReal (((j.factorial : ℝ)) ^ 2) * CoarseFluxDiff.fluxDensity ρ m π G t := by
  unfold fluxInt CoarseFluxDiff.fluxDensity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [mul_left_comm]
  refine mul_le_mul_right ?_ _
  have hc : ∀ k : Fin 2, ∀ x, (orderedDerivative β (fun x' => G t x' k) x) v =
      orderedDerivative β (fun x' => G t x' k v) x := fun k x =>
    (congrFun (orderedDerivative_clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) β
      (hG k)) x).symm
  have hm : ∀ k : Fin 2, AEMeasurable (fun x => ‖(rs ^ j • orderedDerivative β
      (fun x' => G t x' k) x) v‖ₑ ^ 2) (volume.restrict unitCube) := fun k =>
    (((continuous_apply v).comp ((continuous_orderedDerivative β (hG k)).const_smul
      (rs ^ j))).enorm.measurable.pow_const 2).aemeasurable
  rw [lintegral_finsetSum' _ fun k _ => hm k, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  calc ∫⁻ x in unitCube, ‖(rs ^ j • orderedDerivative β (fun x' => G t x' k) x) v‖ₑ ^ 2
      = ∫⁻ x in unitCube, ‖rs ^ j • orderedDerivative β (fun x' => G t x' k v) x‖ₑ ^ 2 := by
        refine lintegral_congr fun x => ?_
        rw [Pi.smul_apply, hc k x]
    _ ≤ _ := CoarseFluxDiff.lintegral_rs_word_le hrs hρ hjm β _

end Slices

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The residual flux of the Galerkin approximant** is the residual flux of the approximant
with the flux approximant. -/
theorem approxFlux_eq_reconResFlux (α q : ℝ) (Λ m : ℕ) (φs : ℝ → Vec 2 → ℝ)
    (hφs : IsAdmissibleStream φs) (ν B ρ tA tZ : ℝ) (ϖ : ℤ → ℝ → ℝ) (H N Acl : ℕ)
    (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) (n : ℕ) {k : ℕ}
    (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) (s : ℝ) (x : Vec 2) :
    approxFlux α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl Vc Vn n Fc v s x =
      WithLp.toLp 2 (fun a₀ => reconResFlux α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl Vc Vn
        (fun t x' a₀' => fluxApprox n (fun v => Fc v t) x' a₀') s x a₀ v) := rfl

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

/-- **The glued tail flux and force are of class `C^r`** at a time of the window. -/
theorem ReconWindowAt.glued_tail_contDiff
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r m' : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift) (hrL : r ≤ Llift)
    (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
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
    {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (hu : ContDiff ℝ ((m' + 1 : ℕ) : ℕ∞) (u t)) :
    (∀ a₀ : Fin 2, ContDiff ℝ (r : ℕ∞) (fun x => gluedTailFlux (ocObsPulses α q Λ m tp (tp + Tobs))
        (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t x a₀)) ∧
    ContDiff ℝ (r : ℕ∞) (fun x => gluedTailForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k =>
        F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t x) := by
  classical
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  set S' := (ocObsPulses α q Λ m tp (tp + Tobs)).filter (fun k => F.weight (pp k) t ≠ 0)
    with hS'
  have hmem : ∀ k ∈ S', k ∈ ocObsPulses α q Λ m tp (tp + Tobs) ∧ F.weight (pp k) t ≠ 0 :=
    fun k hk => Finset.mem_filter.1 hk
  have hwin : ∀ k ∈ S', t ∈ ocPulseWindow α q Λ m k := fun k hk =>
    w.hpart.2.2.2.1 k (hmem k hk).1 t (hmem k hk).2
  have hcell : ∀ k ∈ S', (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    fun k hk => AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 (hwin k hk) ht
  have hcd := fun k (hk : k ∈ S') => w.pulse_tail_contDiff hAcl hK hrL hord u (Vc k)
    (hmem k hk).1 ht (hwin k hk) hu (fun hh hhh => hV k (hmem k hk).1 hh hhh _ (hcell k hk))
  refine ⟨fun a₀ => ?_, ?_⟩
  · have e : (fun x => gluedTailFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t x a₀) = fun x => ∑ k ∈ S',
        F.weight (pp k) t • tailFluxPhys
          (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (Vc k) t x a₀ :=
      funext fun x => sum_smul_eq_sum_filter_weight _ (fun k => F.weight (pp k) t) _
    rw [e]
    exact ContDiff.sum fun k hk => ((hcd k hk).1 a₀).const_smul _
  · have e : (fun x => gluedTailForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp
      k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t x) = fun x => ∑ k ∈ S',
        F.weight (pp k) t • tailForcePhys
          (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (Vc k) t x :=
      funext fun x => sum_smul_eq_sum_filter_weight _ (fun k => F.weight (pp k) t) _
    rw [e]
    exact ContDiff.sum fun k hk => (hcd k hk).2.const_smul _

/-- **The glued lifted flux and force are of class `C^r`** at a time of the window. -/
theorem ReconWindowAt.glued_lift_contDiff
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r : ℕ} (hAcl : 1 ≤ Acl) (hrL : r ≤ Llift)
    (G : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
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
    {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) :
    (∀ a₀ : Fin 2, ContDiff ℝ (r : ℕ∞) (fun x => gluedLiftFlux (ocObsPulses α q Λ m tp (tp + Tobs))
        (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t x a₀)) ∧
    ContDiff ℝ (r : ℕ∞) (fun x => gluedLiftForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k =>
        F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t x) := by
  classical
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  set S' := (ocObsPulses α q Λ m tp (tp + Tobs)).filter (fun k => F.weight (pp k) t ≠ 0)
    with hS'
  have hmem : ∀ k ∈ S', k ∈ ocObsPulses α q Λ m tp (tp + Tobs) ∧ F.weight (pp k) t ≠ 0 :=
    fun k hk => Finset.mem_filter.1 hk
  have hwin : ∀ k ∈ S', t ∈ ocPulseWindow α q Λ m k := fun k hk =>
    w.hpart.2.2.2.1 k (hmem k hk).1 t (hmem k hk).2
  have hcell : ∀ k ∈ S', (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    fun k hk => AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 (hwin k hk) ht
  have hcd := fun k (hk : k ∈ S') => w.pulse_lift_contDiff (k := k) hAcl hrL _ (Vn k)
    (fun hh hhh n' hn' => hVn k (hmem k hk).1 hh hhh n' hn' _ (hcell k hk))
  refine ⟨fun a₀ => ?_, ?_⟩
  · have e : (fun x => gluedLiftFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t x a₀) = fun x => ∑ k ∈ S',
        F.weight (pp k) t • liftFluxPhys
          (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (Vn k) t x a₀ :=
      funext fun x => sum_smul_eq_sum_filter_weight _ (fun k => F.weight (pp k) t) _
    rw [e]
    exact ContDiff.sum fun k hk => ((hcd k hk).1 a₀).const_smul _
  · have e : (fun x => gluedLiftForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp
      k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t x) = fun x => ∑ k ∈ S',
        F.weight (pp k) t • liftForcePhys
          (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (Vn k) t x :=
      funext fun x => sum_smul_eq_sum_filter_weight _ (fun k => F.weight (pp k) t) _
    rw [e]
    exact ContDiff.sum fun k hk => (hcd k hk).2.const_smul _

/-- **The weighted word derivatives of the residual flux at one time of the window.** -/
theorem ReconWindowAt.resFlux_word_le
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
    (hrsρ : rs ≤ ρ) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) :
    fluxInt π (fun x a₀ => rs ^ j • orderedDerivative β (fun x' =>
        reconResFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Vc Vn G t x' a₀) x) ≤
      3 * (ENNReal.ofReal (tailPhysConst H Nc D Acl r m' (pulseChartD Nχ)) *
          ENNReal.ofReal (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          ocEpsilon q Λ m * ρ *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) *
          ResidualTimeData.gradDensity π ρ m' u t +
        ENNReal.ofReal (((j.factorial : ℝ)) ^ 2) *
          CoarseFluxDiff.fluxDensity ρ kres π G t +
        ENNReal.ofReal (liftPhysConst H Nc Acl r kres Nχ (pulseChartD Nχ)) *
          ENNReal.ofReal ((ocEpsilon q Λ m / ρ) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2) *
          CoarseFluxDiff.fluxDensity ρ kres π G t) := by
  have hT := (w.glued_tail_contDiff hAcl hK hrL hord u Vc hV ht hu).1
  have hL := (w.glued_lift_contDiff hAcl hrL G Vn hVn ht).1
  have hjr : (((j : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((r : ℕ) : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hj
  have hGt : ∀ a₀ : Fin 2, ContDiff ℝ (j : ℕ∞) (fun x => G t x a₀) := fun a₀ =>
    (hG t a₀).of_le (by exact_mod_cast (by omega : j ≤ kres + 2))
  refine (fluxInt_word_add_three_le
    (fun x' a₀ => gluedTailFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t x' a₀)
    (fun x' a₀ => G t x' a₀)
    (fun x' a₀ => gluedLiftFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t x' a₀)
    (fun a₀ => (hT a₀).of_le hjr) hGt (fun a₀ => (hL a₀).of_le hjr) rs β π).trans ?_
  refine mul_le_mul_right (add_le_add (add_le_add ?_ ?_) ?_) 3
  · exact (w.glued_tail_slice hAcl hK hrL hord hNχ u Vc hV ht hu hup hrs hrse hj β).1
  · exact fluxInt_word_le_fluxDensity π hrs hrsρ (by omega) β G t hGt
  · exact (w.glued_lift_slice hSb hAcl hK hrL hk hNχ' hCg hgr G hG Vn hVn ht hGp hrs hrse hj
      β).1

/-- **The weighted word derivatives of the residual force at one time of the window.** -/
theorem ReconWindowAt.resForce_word_le
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
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m) {j : ℕ} (hj : j ≤ r)
    (β : DerivativeWord2 j) :
    scalInt π (fun x => rs ^ j • orderedDerivative β (fun x' =>
        reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Vc Vn t x') x) ≤
      2 * (ENNReal.ofReal (tailForceConst H Nc D Acl r m' (pulseChartD Nχ)) *
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
          CoarseFluxDiff.fluxDensity ρ kres π G t) := by
  have hT := (w.glued_tail_contDiff hAcl hK hrL hord u Vc hV ht hu).2
  have hL := (w.glued_lift_contDiff hAcl hrL G Vn hVn ht).2
  have hjr : (((j : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((r : ℕ) : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hj
  refine (scalInt_word_add_two_le
    (fun x' => gluedTailForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t x')
    (fun x' => gluedLiftForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t x')
    (hT.of_le hjr) (hL.of_le hjr) rs β π).trans ?_
  refine mul_le_mul_right (add_le_add ?_ ?_) 2
  · exact (w.glued_tail_slice hAcl hK hrL hord hNχ u Vc hV ht hu hup hrs hrse hj β).2
  · exact (w.glued_lift_slice hSb hAcl hK hrL hk hNχ' hCg hgr G hG Vn hVn ht hGp hrs hrse hj
      β).2
end

/-! **Periodicity of the residual pieces on a reconstruction window**. At a time
of the window, the physical tail flux and force of an observed pulse
    (`ReconWindowAt.pulse_tail_periodic`)
and the physical lifted flux and force (`ReconWindowAt.pulse_lift_periodic`) are `ℤ²`-periodic: the
cleanup chains are invariant under the slow translations by `ρ⁻¹ℤ²` and periodic in the fast
variable, `ε_m⁻¹ ∈ ℕ`, and the renewal charts are lattice equivariant. Hence so are the glued
pieces (`ReconWindowAt.glued_tail_periodic`, `ReconWindowAt.glued_lift_periodic`). -/

section
/-- A weighted sum of periodic fields, with the fields of zero weight arbitrary, is periodic. -/
theorem isZ2Periodic_weighted_sum {E : Type*} [AddCommGroup E] [Module ℝ E] {κ : Type*}
    (S : Finset κ) (w : κ → ℝ) (X : κ → Vec 2 → E)
    (hX : ∀ k ∈ S, w k ≠ 0 → IsZ2Periodic (X k)) :
    IsZ2Periodic (fun x => ∑ k ∈ S, w k • X k x) := by
  intro n x
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hw : w k = 0
  · rw [hw, zero_smul, zero_smul]
  · rw [hX k hk hw n x]

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

/-- **The tail flux and force of one observed pulse are periodic** at a time of the window and
of the window of the pulse. -/
theorem ReconWindowAt.pulse_tail_periodic
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {sXc sZc Acl : ℕ} (hAcl : 1 ≤ Acl) (hZc : 1 ≤ sZc)
    (u : ℝ → Vec 2 → ∀ i, h i) (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    {k : ℤ} (hk : k ∈ ocObsPulses α q Λ m tp (tp + Tobs)) {t : ℝ}
    (ht : t ∈ Set.Icc tp (tp + Tobs)) (hwin : t ∈ ocPulseWindow α q Λ m k)
    (hup : IsZ2Periodic (u t))
    (hV : ∀ hh, hh ≤ H → IsCleanupChain sXc sZc Acl
      (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
        (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
          (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
          (ρ • X))) ((ocEll q Λ m ν ^ 2)⁻¹ * t))
      (tailFluxField (fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1))
          hφ ν B ρ
          (ρ / ocEpsilon q Λ (m - 1)) k
          (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n) Nc D
        (ocDStar q Λ m ν B / ρ)
        (fun s' X => u (ocEll q Λ m ν ^ 2 * s') (ocChart α q Λ m (Φ (m - 1)) hφ
          (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s')
          (ρ • X))) ((ocEll q Λ m ν ^ 2)⁻¹ * t))
      (fun j => Vc hh j ((ocEll q Λ m ν ^ 2)⁻¹ * t))) :
    (∀ a₀ : Fin 2, IsZ2Periodic (fun x => tailFluxPhys (ocChartInv α q Λ m (Φ (m - 1)) hφ
        (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vc t x a₀)) ∧
    IsZ2Periodic (fun x => tailForcePhys (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ
        m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vc t x) := by
  have P := w.hsetting k hk
  have hseq := w.hseq k hk
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hρ : 0 < ρ := P.ρ_pos
  have hcell : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 hwin ht
  have hct : ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]
  obtain ⟨M, hM⟩ := pulse_e_inv_nat q Λ m
  have hψl : ∀ (n : Fin 2 → ℤ) (x : Vec 2),
      ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t (x + latticeShift n) =
        ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t x + latticeShift n :=
    fun n x => CycleReference.streamFlow_lattice_equivariant hφ _ t x n
  have hslow : ∀ hh, hh ≤ H → ∀ j', j' < Acl → ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      Vc hh j' ((ocEll q Λ m ν ^ 2)⁻¹ * t)
          (X + ρ⁻¹ • latticeShift n) =
        Vc hh j' ((ocEll q Λ m ν ^ 2)⁻¹ * t) X := by
    intro hh hhh j' hj' n X
    refine setting_tail_cleanupChain_slowShift P (Klift + D + 2) (max (Llift + 1) (Llift + 2))
      (by omega) (by omega) (Cc k) hseq (ρ⁻¹ • latticeShift n)
      (pulse_G_slow_invariant α q Λ m ζ hφ ν B hρ.ne' _ k _ n)
      (pulse_edge_slow_invariant α q Λ m ζ hφ ν B hρ.ne' k w.htorus (pp k) n)
      hh hhh hZc _ _ _ hcell ?_ (hV hh hhh) j' hj' X
    intro X'
    simp only [hct, smul_add, smul_inv_smul₀ hρ.ne',
      Charts.ocChart_latticeShift hφ α q Λ m (ocPulseChartIndex α q Λ m k) t n]
    exact hup n _
  have hfast : ∀ hh, hh ≤ H → ∀ j', j' < Acl → ∀ X,
      IsZ2Periodic (Vc hh j' ((ocEll q Λ m ν ^ 2)⁻¹ * t) X) := fun hh hhh =>
    (hV hh hhh).periodic (tailFluxField_isZ2Periodic_of_presentation (f := fun _ => 0)
      (F := fun n => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
        ρ
        (ρ / ocEpsilon q Λ (m - 1)) k
        (F.fiber (pp k) (actual (pp k)))) (Cc k) Nc hh n)
      (fun n hn1 hn2 => setting_tail_presentation P (Klift + D + 2) (max (Llift + 1) (Llift + 2))
        (by omega) (by omega) (Cc k) hseq hh hhh n (by omega) hn2) _ _ hcell)
  refine ⟨fun a₀ => tailFluxPhys_isZ2Periodic hψl H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vc t
    (tailFluxLabel_isZ2Periodic H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vc t M hM hslow hfast) a₀, ?_⟩
  intro n x
  show ∑ hh ∈ Finset.range (H + 1), (ocEll q Λ m ν ^ 2)⁻¹ •
      (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) •
      cleanupRemainder (ocEll q Λ m ν ^ 2)⁻¹ ρ (ocEpsilon q Λ m)
        Acl (Vc hh) t ((ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) (x +
            latticeShift n)) =
    ∑ hh ∈ Finset.range (H + 1), (ocEll q Λ m ν ^ 2)⁻¹ •
      (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) •
      cleanupRemainder (ocEll q Λ m ν ^ 2)⁻¹ ρ (ocEpsilon q Λ m)
        Acl (Vc hh) t ((ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) x)
  refine Finset.sum_congr rfl fun hh hhm => ?_
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
  have hr : cleanupRemainder (ocEll q Λ m ν ^ 2)⁻¹ ρ
      (ocEpsilon q Λ m) Acl (Vc hh) t
      (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t x + latticeShift n) =
      cleanupRemainder (ocEll q Λ m ν ^ 2)⁻¹ ρ
        (ocEpsilon q Λ m) Acl (Vc hh) t
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t x) :=
    cleanupRemainder_isZ2Periodic _ _ _ hAcl (Vc hh) t M hM (hslow hh hhh) (hfast hh hhh) n _
  rw [hψl n x, hr]

/-- **The lifted flux and force of one observed pulse are periodic** at a time of the window and
of the window of the pulse. -/
theorem ReconWindowAt.pulse_lift_periodic
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {sXl sZl Acl : ℕ} (hAcl : 1 ≤ Acl) (hZl : 1 ≤ sZl)
    (G : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    {k : ℤ} (hk : k ∈ ocObsPulses α q Λ m tp (tp + Tobs)) {t : ℝ}
    (ht : t ∈ Set.Icc tp (tp + Tobs)) (hwin : t ∈ ocPulseWindow α q Λ m k)
    (hGp : ∀ k', IsZ2Periodic (fun x => G t x k'))
    (hV : ∀ hh, hh ≤ H → ∀ n', n' < Nc → IsCleanupChain sXl sZl Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
          fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k')
            (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
              (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k'))
          ((ocEll q Λ m ν ^ 2)⁻¹ * t))
        (fun _ _ _ => 0) (fun j => Vn hh n' j ((ocEll q Λ m ν ^ 2)⁻¹ * t))) :
    (∀ a₀ : Fin 2, IsZ2Periodic (fun x => liftFluxPhys (ocChartInv α q Λ m (Φ (m - 1)) hφ
        (ocPulseChartIndex α q Λ m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vn t x a₀)) ∧
    IsZ2Periodic (fun x => liftForcePhys (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ
        m k) t) H Nc Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) Vn t x) := by
  have P := w.hsetting k hk
  have hseq := w.hseq k hk
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hρ : 0 < ρ := P.ρ_pos
  have hcell : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 hwin ht
  have hct : ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]
  obtain ⟨M, hM⟩ := pulse_e_inv_nat q Λ m
  have hψl : ∀ (n : Fin 2 → ℤ) (x : Vec 2),
      ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t (x + latticeShift n) =
        ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t x + latticeShift n :=
    fun n x => CycleReference.streamFlow_lattice_equivariant hφ _ t x n
  have hslow : ∀ n', n' < Nc → ∀ hh, hh ≤ H → ∀ j', j' < Acl → ∀ (n : Fin 2 → ℤ)
      (X : Vec 2), Vn hh n' j' ((ocEll q Λ m ν ^ 2)⁻¹ * t)
          (X + ρ⁻¹ • latticeShift n) =
        Vn hh n' j' ((ocEll q Λ m ν ^ 2)⁻¹ * t) X := by
    intro n' hn' hh hhh j' hj' n X
    refine isCleanupChain_slow_invariant hZl
      (ρ⁻¹ • latticeShift n) (fun X' => ?_) (fun _ => rfl)
      (hV hh hhh n' hn') j' hj' X
    funext z
    refine liftApply_slow_invariant (n' + 1) (Cc k hh (n' + 1)) _ ((ocEll q Λ m ν ^ 2)⁻¹ * t)
      (ρ⁻¹ • latticeShift n)
      (fun m' α' X'' z' v' u' =>
        LiftMeanEntrywise.setting_liftSequence_slowShift_invariant P _ _ (Cc k) hseq
          (ρ⁻¹ • latticeShift n)
          (pulse_G_slow_invariant α q Λ m ζ hφ ν B hρ.ne' _ k _ n)
          (pulse_edge_slow_invariant α q Λ m ζ hφ ν B hρ.ne' k w.htorus (pp k) n) hh hhh
          (n' + 1) m' α' _ hcell X'' z' v' u') (fun X₁ => ?_) X' z
    simp only [hct, smul_add, smul_inv_smul₀ hρ.ne',
      Charts.ocChart_latticeShift hφ α q Λ m (ocPulseChartIndex α q Λ m k) t n]
    refine Finset.sum_congr rfl fun k' _ => ?_
    have hd : (fun y => G t (y + latticeShift n) k') = fun y => G t y k' :=
      funext fun y => hGp k' n y
    have h2 : fderiv ℝ (fun y => G t (y + latticeShift n) k')
        (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t
          (ρ • X₁)) =
      fderiv ℝ (fun y => G t y k') (ocChart α q Λ m (Φ (m - 1)) hφ
        (ocPulseChartIndex α q Λ m k) t (ρ • X₁) +
          latticeShift n) :=
      fderiv_comp_add_right (𝕜 := ℝ) (f := fun y => G t y k') (latticeShift n)
    rw [hd] at h2
    rw [← h2]
  have hfast : ∀ n', n' < Nc → ∀ hh, hh ≤ H → ∀ j', j' < Acl → ∀ X,
      IsZ2Periodic (Vn hh n' j' ((ocEll q Λ m ν ^ 2)⁻¹ * t) X) := fun n' hn' hh hhh =>
    (hV hh hhh n' hn').periodic (F₀ := fun _ _ _ => 0) (fun _ _ _ => rfl)
  refine ⟨fun a₀ => ?_, ?_⟩
  · refine isZ2Periodic_weighted_sum (Finset.range Nc) (fun _ => ocEll q Λ m ν ^ 2)
      (fun n' x => tailFluxPhys (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t)
          H n' Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) (fun hh => Vn hh n') t x a₀)
      fun n' hn' _ => ?_
    have hn'' := Finset.mem_range.1 hn'
    exact tailFluxPhys_isZ2Periodic hψl H n' Acl _ _ _ _ (fun hh => Vn hh n') t
      (tailFluxLabel_isZ2Periodic H n' Acl _ _ _ _ (fun hh => Vn hh n') t M hM
        (hslow n' hn'') (hfast n' hn'')) a₀
  · refine isZ2Periodic_weighted_sum (Finset.range Nc) (fun _ => ocEll q Λ m ν ^ 2)
      (fun n' x => tailForcePhys (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t)
          H n' Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
        ρ (ocEpsilon q Λ m) (fun hh => Vn hh n') t x)
      fun n' hn' _ => ?_
    have hn'' := Finset.mem_range.1 hn'
    intro n x
    show ∑ hh ∈ Finset.range (H + 1), (ocEll q Λ m ν ^ 2)⁻¹ •
        (ocDStar q Λ m ν B / ρ) ^ (n' + 1) •
        cleanupRemainder (ocEll q Λ m ν ^ 2)⁻¹ ρ
          (ocEpsilon q Λ m) Acl (Vn hh n') t ((ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex
              α q Λ m k) t) (x + latticeShift n)) =
      ∑ hh ∈ Finset.range (H + 1), (ocEll q Λ m ν ^ 2)⁻¹ •
        (ocDStar q Λ m ν B / ρ) ^ (n' + 1) •
        cleanupRemainder (ocEll q Λ m ν ^ 2)⁻¹ ρ
          (ocEpsilon q Λ m) Acl (Vn hh n') t ((ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex
              α q Λ m k) t) x)
    refine Finset.sum_congr rfl fun hh hhm => ?_
    have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
    have hr : cleanupRemainder (ocEll q Λ m ν ^ 2)⁻¹ ρ
        (ocEpsilon q Λ m) Acl (Vn hh n') t
        (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t x + latticeShift n) =
        cleanupRemainder (ocEll q Λ m ν ^ 2)⁻¹ ρ
          (ocEpsilon q Λ m) Acl (Vn hh n') t
          (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t x) :=
      cleanupRemainder_isZ2Periodic _ _ _ hAcl (Vn hh n') t M hM (hslow n' hn'' hh hhh)
        (hfast n' hn'' hh hhh) n _
    rw [hψl n x, hr]

/-- **The glued tail flux and force are periodic** at a time of the window. -/
theorem ReconWindowAt.glued_tail_periodic
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {sXc sZc Acl : ℕ} (hAcl : 1 ≤ Acl) (hZc : 1 ≤ sZc)
    (u : ℝ → Vec 2 → ∀ i, h i) (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
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
        (fun j => Vc k hh j τ))
    {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (hup : IsZ2Periodic (u t)) :
    (∀ a₀ : Fin 2, IsZ2Periodic (fun x => gluedTailFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k
        => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t x a₀)) ∧
    IsZ2Periodic (fun x => gluedTailForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight
        (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t x) := by
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hwin : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), F.weight (pp k) t ≠ 0 →
      t ∈ ocPulseWindow α q Λ m k := fun k hk hw => w.hpart.2.2.2.1 k hk t hw
  have hcell : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), F.weight (pp k) t ≠ 0 →
      (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    fun k hk hw =>
      AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 (hwin k hk hw) ht
  have hp := fun k (hk : k ∈ ocObsPulses α q Λ m tp (tp + Tobs)) (hw : F.weight (pp k) t ≠ 0) =>
    w.pulse_tail_periodic hAcl hZc u (Vc k) hk ht (hwin k hk hw) hup
      (fun hh hhh => hV k hk hh hhh _ (hcell k hk hw))
  exact ⟨fun a₀ => isZ2Periodic_weighted_sum _ (fun k => F.weight (pp k) t) _
    fun k hk hw => (hp k hk hw).1 a₀,
    isZ2Periodic_weighted_sum _ (fun k => F.weight (pp k) t) _ fun k hk hw => (hp k hk hw).2⟩

/-- **The glued lifted flux and force are periodic** at a time of the window. -/
theorem ReconWindowAt.glued_lift_periodic
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {sXl sZl Acl : ℕ} (hAcl : 1 ≤ Acl) (hZl : 1 ≤ sZl)
    (G : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hVn : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXl sZl Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
          fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k')
            (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
              (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k'))
          τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n' j τ))
    {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (hGp : ∀ k', IsZ2Periodic (fun x => G t x k')) :
    (∀ a₀ : Fin 2, IsZ2Periodic (fun x => gluedLiftFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k
        => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t x a₀)) ∧
    IsZ2Periodic (fun x => gluedLiftForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight
        (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t x) := by
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hwin : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), F.weight (pp k) t ≠ 0 →
      t ∈ ocPulseWindow α q Λ m k := fun k hk hw => w.hpart.2.2.2.1 k hk t hw
  have hcell : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), F.weight (pp k) t ≠ 0 →
      (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    fun k hk hw =>
      AVRegularity.CycleComparison.Assembly.cellTime_mem_liftWindow hc0 (hwin k hk hw) ht
  have hp := fun k (hk : k ∈ ocObsPulses α q Λ m tp (tp + Tobs)) (hw : F.weight (pp k) t ≠ 0) =>
    w.pulse_lift_periodic hAcl hZl G (Vn k) hk ht (hwin k hk hw) hGp
      (fun hh hhh n' hn' => hVn k hk hh hhh n' hn' _ (hcell k hk hw))
  exact ⟨fun a₀ => isZ2Periodic_weighted_sum _ (fun k => F.weight (pp k) t) _
    fun k hk hw => (hp k hk hw).1 a₀,
    isZ2Periodic_weighted_sum _ (fun k => F.weight (pp k) t) _ fun k hk hw => (hp k hk hw).2⟩

/-- **The residual flux and force are periodic** at a time of the window. -/
theorem ReconWindowAt.res_periodic
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {sXc sZc sXl sZl Acl : ℕ} (hAcl : 1 ≤ Acl) (hZc : 1 ≤ sZc) (hZl : 1 ≤ sZl)
    (u : ℝ → Vec 2 → ∀ i, h i) (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
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
        (fun j => Vc k hh j τ))
    (G : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hVn : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXl sZl Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s' X => ∑ k' : Fin 2,
          fderiv ℝ (fun x => G (ocEll q Λ m ν ^ 2 * s') x k')
            (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)
              (ocEll q Λ m ν ^ 2 * s') (ρ • X)) (basisVec k'))
          τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n' j τ))
    {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (hup : IsZ2Periodic (u t))
    (hGp : ∀ k', IsZ2Periodic (fun x => G t x k')) :
    (∀ a₀ : Fin 2, IsZ2Periodic (fun x => reconResFlux α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Vc Vn G t x a₀)) ∧
    IsZ2Periodic (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Vc Vn t x) := by
  obtain ⟨hT, hTf⟩ := w.glued_tail_periodic hAcl hZc u Vc hV ht hup
  obtain ⟨hL, hLf⟩ := w.glued_lift_periodic hAcl hZl G Vn hVn ht hGp
  refine ⟨fun a₀ n x => ?_, fun n x => ?_⟩
  · show gluedTailFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t (x + latticeShift n) a₀ +
        G t (x + latticeShift n) a₀ + gluedLiftFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k =>
            F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t (x + latticeShift n) a₀ =
      gluedTailFlux (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t x a₀ + G t x a₀ + gluedLiftFlux
              (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t x a₀
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (hT a₀ n x) (hGp a₀ n x)) (hL a₀ n x)
  · show gluedTailForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t (x + latticeShift n) +
        gluedLiftForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t (x + latticeShift n) =
      gluedTailForce (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vc t x + gluedLiftForce (ocObsPulses α
              q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) H Nc Acl
          (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) Vn t x
    exact congrArg₂ (· + ·) (hTf n x) (hLf n x)
end

end AVRegularity.CycleComparison.Reconstruction
end
