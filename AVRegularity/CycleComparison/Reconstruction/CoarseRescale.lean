-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.PulseChart
import AVRegularity.CycleComparison.Reconstruction.TailSample
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleLiftIdentity
import AVRegularity.CycleComparison.Assembly.CoarseLetters
public import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The source part of the pulse density is the divergence of the edge flux**.

The rest `labelRest` of the label density contains the sources `𝒮_ε Φ_{hh-1}` of the lower
grades: its source part `labelSourcePart`. For the lift of one piece `p₀` of a charted family,
`Q.edge = liftEdges c lam (F.fiber p₀ c₀)`:

* `source_part_top_vanish`: on the window the source of the top grade `H` vanishes (the source
  graph has depth at most `H`), so the source part is the sum of the sources of all grades `≤ H`;
* `source_part_label_div`: with `c⁻¹ e (e/ν) = 1`, `c⁻¹` times the source part at the label `y`
  is the label divergence of the label edge flux of the full label lift `V = labelLift …`. Each
  grade is `sourceOp_lift_eq_label_of_contDiff`; the label edge flux is additive in the field
  (`labelEdgeFlux_finsetSum`) and the flux of each grade is differentiable, being the sample of
  the box smooth source flux (`labelEdgeFlux_sample_differentiable`);
* if, at time `t`, the flux term of the actual equation for
  the physical lift `U = V ∘ ψ` is the Piola transport of the label edge flux of `p₀`, then `c⁻¹`
  times the source part at `ψ x` is the physical divergence of the flux term at `x`
  (`chartInvJacobian_piola`, `div_eq_label_div_of_transported`). This applies at a single-piece
  time and at a quiet overlap.
-/

section Sums

/-- Commuting a sum over a finite set with a dependent double sum. -/
theorem sum_dep_finset_comm {M : Type*} [AddCommMonoid M] {α : Type*} {κ : α → Type*}
    [∀ a, Fintype (κ a)] {T : Type*} (s : Finset α) (S : Finset T) (f : ∀ a, κ a → T → M) :
    ∑ a ∈ s, ∑ b : κ a, ∑ j ∈ S, f a b j = ∑ j ∈ S, ∑ a ∈ s, ∑ b : κ a, f a b j :=
  Eq.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm) Finset.sum_comm

end Sums

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {Pc : Type*} {Ctx : Pc → Type*}

omit [Fintype ι] in
/-- A coordinate of the derivative of a vector field differentiable at `y` is the derivative of
the coordinate. -/
theorem fderiv_pi_coord {f : Vec 2 → ∀ i, h i} {y : Vec 2} (hf : DifferentiableAt ℝ f y)
    (w : Vec 2) (v : ι) : fderiv ℝ f y w v = fderiv ℝ (fun y' => f y' v) y w := by
  simp only [_root_.fderiv_apply hf v, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

/-- **The label edge flux is additive in the field** over finitely many `C^r` fields, `D ≤ r + 1`
(the label words of the flux have length `≤ D - 1`). -/
theorem labelEdgeFlux_finsetSum (F : ChartedFamily ι h D Pc Ctx) (ν e E : ℝ) (p : Pc)
    (c : Ctx p) (t : ℝ) {κ : Type*} (S : Finset κ) (W : κ → Vec 2 → ∀ i, h i) {r : ℕ}
    (hW : ∀ j ∈ S, ContDiff ℝ (r : ℕ∞) (W j)) (hrD : D ≤ r + 1) (v : ι) (y : Vec 2)
    (i₀ : Fin 2) :
    labelEdgeFlux F ν e E p c t (fun y' => ∑ j ∈ S, W j y') v y i₀ =
      ∑ j ∈ S, labelEdgeFlux F ν e E p c t (W j) v y i₀ := by
  have hI : ∀ (u : ι) (γ : F.Γ v u) (d : ℕ), d ∈ Finset.Icc 1 (F.identity v u γ).maxOrder →
      ∀ I : DerivativeWord2 (d - 1),
        orderedDerivative I (fun y' => (∑ j ∈ S, W j y') u) y =
          ∑ j ∈ S, orderedDerivative I (fun y' => W j y' u) y := by
    intro u γ d hd I
    have hle := (F.identity v u γ).le_D
    have hdm := (Finset.mem_Icc.mp hd).2
    have hfun : (fun y' => (∑ j ∈ S, W j y') u) = fun y' => ∑ j ∈ S, W j y' u :=
      funext fun y' => Finset.sum_apply u S fun j => W j y'
    refine (congrArg (fun g : Vec 2 → h u => orderedDerivative I g y) hfun).trans ?_
    exact congrFun (MixedTail.orderedDerivative_sum S I (g := fun q y' => W q y' u)
      fun q hq => (contDiff_pi.1 (hW q hq) u).of_le
        (by exact_mod_cast (show d - 1 ≤ r by omega))) y
  have hγ : ∀ (u : ι) (γ : F.Γ v u), (F.identity v u γ).map
        (∑ d ∈ Finset.Icc 1 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
          F.dimFlux ν e E p c v u γ d I t y (e⁻¹ • y) i₀ •
            orderedDerivative I (fun y' => (∑ j ∈ S, W j y') u) y) =
      ∑ j ∈ S, (F.identity v u γ).map
        (∑ d ∈ Finset.Icc 1 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
          F.dimFlux ν e E p c v u γ d I t y (e⁻¹ • y) i₀ •
            orderedDerivative I (fun y' => W j y' u) y) := by
    intro u γ
    rw [← map_sum, Finset.sum_comm (s := S)]
    refine congrArg (fun z => (F.identity v u γ).map z) (Finset.sum_congr rfl fun d hd => ?_)
    rw [Finset.sum_comm (s := S)]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hI u γ d hd I, Finset.smul_sum]
  simp only [labelEdgeFlux]
  refine Eq.trans (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun γ _ => hγ u γ) ?_
  exact sum_dep_finset_comm _ S _

/-- The two-scale sample of the source flux of an edge family with `(1, 1)` box smooth
coefficients, applied to a `(D, D)` box smooth field, is differentiable. -/
theorem sample_sourceFlux_differentiable (edge : ConstituentEdges D h) (η ε s ρ e : ℝ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth 1 1 (fun X z => γ.coeff α s X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : IsBoxSmooth D D Φ) (k : Fin 2) :
    Differentiable ℝ (twoScaleSample ρ e (sourceFlux edge η ε s Φ k)) := by
  have hS : ContDiff ℝ 1 (twoScaleSample ρ e (sourceFlux edge η ε s Φ k)) :=
    CoarseFluxDiff.contDiff_sample (isBoxSmooth_sourceFlux edge η ε s Φ k hΓ hΦ (by omega))
      le_rfl le_rfl ρ e
  exact hS.differentiable one_ne_zero

/-- **The scaled label edge flux of a sampled field is the sample of the source flux** of the
lifted fiber: `(e/ν) G(cℓ s)(SΦ)_k = S(flux_k Φ)`, for `√η ε = e/ρ`, `lam ρ⁻¹ = E⁻¹`. -/
theorem scaledLabelEdgeFlux_eq_sample (F : ChartedFamily ι h D Pc Ctx) (ν e E : ℝ) (p : Pc)
    (c : Ctx p) (cℓ : ℝ) {η ε ρ lam : ℝ} (he : e ≠ 0) (hν : ν ≠ 0)
    (hscale : Real.sqrt η * ε = e * ρ⁻¹) (hlam : lam * ρ⁻¹ = E⁻¹) (s : ℝ)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : IsBoxSmooth D D Φ) (k : Fin 2) :
    (fun (y' : Vec 2) (v : ι) =>
        (e / ν) • labelEdgeFlux F ν e E p c (cℓ * s) (twoScaleSample ρ e Φ) v y' k) =
      twoScaleSample ρ e (sourceFlux (liftEdges cℓ lam (F.fiber p c)) η ε s Φ k) := by
  have hV : ContDiff ℝ (D : ℕ∞) (twoScaleSample ρ e Φ) :=
    CoarseFluxDiff.contDiff_sample hΦ le_rfl le_rfl ρ e
  exact funext fun y' => funext fun v =>
    ((sample_sourceFlux (liftEdges cℓ lam (F.fiber p c)) he hscale s hΦ k y' v).trans
      (liftFlux_eq_labelEdgeFlux_of_contDiff F ν e E p c cℓ lam ρ s hlam hν hV
        (Nat.le_succ D) v y' k)).symm

/-- **The label edge flux of a sampled field is differentiable** when the field is `(D, D)` and
the lifted coefficients `(1, 1)` box smooth (scale laws as in
`sourceOp_lift_apply_eq_labelDiv`). -/
theorem labelEdgeFlux_sample_differentiable (F : ChartedFamily ι h D Pc Ctx) (ν e E : ℝ)
    (p : Pc) (c : Ctx p) {η ε ρ cℓ lam : ℝ} (he : e ≠ 0) (hν : ν ≠ 0)
    (hscale : Real.sqrt η * ε = e * ρ⁻¹) (hlam : lam * ρ⁻¹ = E⁻¹) {s τ : ℝ} (hτ : cℓ * s = τ)
    (hΓ : ∀ v u d, ∀ γ ∈ liftEdges cℓ lam (F.fiber p c) v u d, ∀ α,
      IsBoxSmooth 1 1 (fun X z => γ.coeff α s X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : IsBoxSmooth D D Φ) (v : ι) (k : Fin 2) :
    Differentiable ℝ (fun y' => labelEdgeFlux F ν e E p c τ (twoScaleSample ρ e Φ) v y' k) := by
  subst hτ
  have h1 := differentiable_pi.1
    (sample_sourceFlux_differentiable (liftEdges cℓ lam (F.fiber p c)) η ε s ρ e hΓ hΦ k) v
  rw [← scaledLabelEdgeFlux_eq_sample F ν e E p c cℓ he hν hscale hlam s hΦ k] at h1
  have h2 : Differentiable ℝ (fun y' => (e / ν)⁻¹ •
      ((e / ν) • labelEdgeFlux F ν e E p c (cℓ * s) (twoScaleSample ρ e Φ) v y' k)) :=
    h1.const_smul (e / ν)⁻¹
  have hinv : (e / ν)⁻¹ * (e / ν) = 1 := inv_mul_cancel₀ (div_ne_zero he hν)
  simp only [smul_smul, hinv, one_smul] at h2
  exact h2

/-- **One grade of the sampled source, component `v`.** The two-scale sample of the source of the
lifted fiber of the piece `p` is `e (e/ν)` times the label divergence of the label edge flux of
`p` at the physical time `τ = cℓ s`, applied to the sampled field. -/
theorem sourceOp_lift_apply_eq_labelDiv (F : ChartedFamily ι h D Pc Ctx) (ν e E : ℝ) (p : Pc)
    (c : Ctx p) {η ε ρ cℓ lam : ℝ} (he : e ≠ 0) (hν : ν ≠ 0)
    (hscale : Real.sqrt η * ε = e * ρ⁻¹) (hlam : lam * ρ⁻¹ = E⁻¹) {s τ : ℝ} (hτ : cℓ * s = τ)
    (hΓ : ∀ v u d, ∀ γ ∈ liftEdges cℓ lam (F.fiber p c) v u d, ∀ α,
      IsBoxSmooth 1 1 (fun X z => γ.coeff α s X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : IsBoxSmooth D D Φ) (y : Vec 2) (v : ι) :
    sourceOp (liftEdges cℓ lam (F.fiber p c)) η ε s Φ (ρ⁻¹ • y) (e⁻¹ • y) v =
      (e * (e / ν)) • ∑ k : Fin 2, fderiv ℝ
        (fun y' => labelEdgeFlux F ν e E p c τ (twoScaleSample ρ e Φ) v y' k) y (basisVec k) := by
  subst hτ
  have hLd : ∀ k : Fin 2, Differentiable ℝ
      (fun y' => labelEdgeFlux F ν e E p c (cℓ * s) (twoScaleSample ρ e Φ) v y' k) := fun k =>
    labelEdgeFlux_sample_differentiable F ν e E p c he hν hscale hlam rfl hΓ hΦ v k
  have hGd : ∀ k : Fin 2, Differentiable ℝ (fun (y' : Vec 2) (v' : ι) =>
      (e / ν) • labelEdgeFlux F ν e E p c (cℓ * s) (twoScaleSample ρ e Φ) v' y' k) := by
    intro k
    have h1 := sample_sourceFlux_differentiable (liftEdges cℓ lam (F.fiber p c)) η ε s ρ e hΓ hΦ k
    rw [← scaledLabelEdgeFlux_eq_sample F ν e E p c cℓ he hν hscale hlam s hΦ k] at h1
    exact h1
  have hV : ContDiff ℝ (D : ℕ∞) (twoScaleSample ρ e Φ) :=
    CoarseFluxDiff.contDiff_sample hΦ le_rfl le_rfl ρ e
  rw [sourceOp_lift_eq_label_of_contDiff F ν e E p c he hν hscale hlam s hΓ hΦ hV
    (Nat.le_succ D) y, Pi.smul_apply, Finset.sum_apply, mul_smul]
  refine congrArg (e • ·) ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine (fderiv_pi_coord ((hGd k) y) (basisVec k) v).trans ?_
  rw [fderiv_fun_const_smul ((hLd k) y) (e / ν), _root_.smul_apply]

end Family

section Piola

/-- **Piola, factored.** If a physical flux `Φf` is, at every point, the transport
`∑_{i₀} K_{a₀ i₀}(x') G(ψ x')_{i₀}` (`K = chartInvJacobian ψ`) of a differentiable label flux `G`
by an area preserving chart `χ = ψ⁻¹`, its physical divergence at `x` is the label divergence of
`G` at `ψ x`. -/
theorem div_eq_label_div_of_transported {Ev : Type*} [NormedAddCommGroup Ev] [NormedSpace ℝ Ev]
    {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (hd : ∀ y, (jacMatrix χ y).det = 1)
    {G : Vec 2 → Fin 2 → Ev} (hG : ∀ l, Differentiable ℝ (fun y => G y l))
    {Φf : Vec 2 → Fin 2 → Ev}
    (hflux : ∀ x' a₀, Φf x' a₀ = ∑ i₀ : Fin 2, chartInvJacobian ψ x' a₀ i₀ • G (ψ x') i₀)
    (x : Vec 2) :
    ∑ a₀ : Fin 2, fderiv ℝ (fun x' => Φf x' a₀) x (basisVec a₀) =
      ∑ i₀ : Fin 2, fderiv ℝ (fun y => G y i₀) (ψ x) (basisVec i₀) := by
  have hfun : ∀ a₀ : Fin 2, (fun x' => Φf x' a₀) =
      fun x' => ∑ i₀ : Fin 2, chartInvJacobian ψ x' a₀ i₀ • G (ψ x') i₀ :=
    fun a₀ => funext fun x' => hflux x' a₀
  refine Eq.trans (Finset.sum_congr rfl fun a₀ _ =>
    congrArg (fun g : Vec 2 → Ev => fderiv ℝ g x (basisVec a₀)) (hfun a₀)) ?_
  exact chartInvJacobian_piola hχ hψ hψχ hχψ hd hG x

end Piola

section Label

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

/-- The source part of `labelRest`: the sources of the grades `hh - 1`, `1 ≤ hh ≤ H`, sampled at
the label `y` and the cell time `c⁻¹ t`. -/
def labelSourcePart {D : ℕ} (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (N H : ℕ) (ε : ℝ) (f : ℝ → Vec 2 → ∀ i, h i) (ρs es c t : ℝ) (y : Vec 2) : ∀ i, h i :=
  ∑ hh ∈ Finset.range (H + 1), (if hh = 0 then 0 else sourceOp Q.edge Q.η ε (c⁻¹ * t)
    (liftPolyField Cc N ε (hh - 1) (fun _ => f (c⁻¹ * t)) (c⁻¹ * t)) (ρs⁻¹ • y) (es⁻¹ • y))

/-- The label lift is the finite sum of the two-scale samples of the grades. -/
theorem labelLift_eq_sum_sample (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε : ℝ)
    (f : ℝ → Vec 2 → ∀ i, h i) (ρs es c t : ℝ) :
    labelLift Cc N H ε f ρs es c t = fun y => ∑ hh ∈ Finset.range (H + 1),
      twoScaleSample ρs es (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t)) y :=
  funext fun _ => rfl

end Label

section Setting

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K₀ k₀ L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {t₀ t₁ e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : Fin 2} {Vsh : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bE : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π t₀ t₁ e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ par Vsh H N K₀ k₀ L qs qf CG
    Cw Cj bE Θ)
  {Pc : Type*} {Ctx : Pc → Type*}

/-! ### Depth: the top grade has no source -/

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- On the window, the lift of the top grade `H` vanishes in every component that does not end an
edge path of length `H`. -/
theorem setting_liftPolyField_top_vanish {sX sZ : ℕ} (hsZ : 1 ≤ sZ)
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (ε : ℝ)
    (A : ℝ → Vec 2 → ∀ i, h i) {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) {u : ι}
    (hu : u ∉ deepSet Q.edge H) (X z : Vec 2) : liftPolyField Cc N ε H A s X z u = 0 := by
  have hu0 : u ∉ deepSet Q.edge (0 + H) := by
    rw [Nat.zero_add]
    exact hu
  show (∑ n ∈ Finset.range (N + 1), ε ^ n • liftApply n (Cc H n) A s X z) u = 0
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [Pi.smul_apply, setting_liftApply_vanish P hsZ hseq le_rfl n hs A (m := 0)
    (fun u' hu' => absurd (Set.mem_univ u') hu') u hu0 X z, smul_zero]

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- **The top grade has no source.** On the window, the source of the lift of grade `H` vanishes:
an edge into `v` from a component carrying the grade-`H` lift would end a path of length
`H + 1`. -/
theorem setting_sourceOp_top_eq_zero {sX sZ : ℕ} (hsZ : 1 ≤ sZ)
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (ε ε' : ℝ)
    (A : ℝ → Vec 2 → ∀ i, h i) {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (X z : Vec 2) :
    sourceOp Q.edge Q.η ε' s (liftPolyField Cc N ε H A s) X z = 0 := by
  funext v
  refine sourceOp_apply_eq_zero (fun u => ?_) ε' X z
  by_cases hE : IsEdge Q.edge u v
  · exact Or.inr fun X' z' => setting_liftPolyField_top_vanish P hsZ hseq ε A hs
      (fun hu => notMem_deepSet_of_depth P.depth v ⟨u, hu, hE⟩) X' z'
  · exact Or.inl fun d => by
      by_contra hd
      exact hE ⟨d, hd⟩

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- **(1) The source part is the sum of the sources of all grades `≤ H`.** On the window, the
shifted sum `∑_{hh ≤ H} [hh ≠ 0] 𝒮_ε Φ_{hh-1}` of the source part of `labelRest` equals
`∑_{hh ≤ H} 𝒮_ε Φ_hh`, the source of the top grade vanishing. -/
theorem source_part_top_vanish {sX sZ : ℕ} (hsZ : 1 ≤ sZ) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (ε : ℝ) (g : Vec 2 → ∀ i, h i) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) (X z : Vec 2) :
    ∑ hh ∈ Finset.range (H + 1), (if hh = 0 then 0 else
        sourceOp Q.edge Q.η ε s (liftPolyField Cc N ε (hh - 1) (fun _ => g) s) X z) =
      ∑ hh ∈ Finset.range (H + 1),
        sourceOp Q.edge Q.η ε s (liftPolyField Cc N ε hh (fun _ => g) s) X z := by
  have hL : ∑ hh ∈ Finset.range (H + 1), (if hh = 0 then 0 else
        sourceOp Q.edge Q.η ε s (liftPolyField Cc N ε (hh - 1) (fun _ => g) s) X z) =
      ∑ i ∈ Finset.range H,
        sourceOp Q.edge Q.η ε s (liftPolyField Cc N ε i (fun _ => g) s) X z := by
    refine (Finset.sum_range_succ' _ H).trans ?_
    rw [ite_eq_left rfl, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ite_eq_right (Nat.add_one_ne_zero i), Nat.add_sub_cancel]
  have hR : ∑ hh ∈ Finset.range (H + 1),
        sourceOp Q.edge Q.η ε s (liftPolyField Cc N ε hh (fun _ => g) s) X z =
      ∑ i ∈ Finset.range H,
        sourceOp Q.edge Q.η ε s (liftPolyField Cc N ε i (fun _ => g) s) X z := by
    rw [Finset.sum_range_succ, setting_sourceOp_top_eq_zero P hsZ hseq ε ε (fun _ => g) hs X z,
      add_zero]
  exact hL.trans hR.symm

/-! ### Regularity of the grades and of the lifted coefficients -/

include P in
/-- On the window the lift coefficients of the degrees `n ≤ N` are box smooth of order
`(D, D)` (the ambient reserves of the setting). -/
theorem setting_lift_coefficient_boxD {sX sZ : ℕ} (hsZ : 1 ≤ sZ)
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {hh : ℕ}
    (hhh : hh ≤ H) {n : ℕ} (hn : n ≤ N) (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) :
    IsBoxSmooth D D (fun X z => Cc hh n m α s X z v u) := by
  have hr : 0 + (N + D) ≤ qs := by
    have := setting_ambient_output_supported P
    omega
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq 0 hr hh hhh n
    (by omega)
  apply (state.coefficient.box m hm α v u s hs).mono
  · unfold ambientDegreeSlowReserve
    omega
  · unfold ambientDegreeFastReserve
    omega

include P in
/-- The truncated lift of a smooth coarse field is box smooth of order `(D, D)` on the window. -/
theorem setting_liftPolyField_boxD {sX sZ : ℕ} (hsZ : 1 ≤ sZ) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {hh : ℕ} (hhh : hh ≤ H) (ε : ℝ)
    (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ (⊤ : ℕ∞) g) {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) :
    IsBoxSmooth D D (liftPolyField Cc N ε hh (fun _ => g) s) :=
  isBoxSmooth_finsetSum _ fun n hn =>
    isBoxSmooth_const_smul (liftApply_box_reserve n D D (Cc hh n) (fun _ => g) s
      (hg.of_le (by simp)) (fun m hm α v u => setting_lift_coefficient_boxD P hsZ hseq hhh
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) m hm α v u hs)) _

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
include P in
/-- If the source edges of the setting are the lifted fiber of a piece, the lifted coefficients
are `(1, 1)` box smooth on the window. -/
theorem setting_liftedEdge_coeff_box (F : ChartedFamily ι h D Pc Ctx) (p₀ : Pc) (c₀ : Ctx p₀)
    {c lam : ℝ} (hQe : Q.edge = liftEdges c lam (F.fiber p₀ c₀)) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) :
    ∀ v u d, ∀ γ ∈ liftEdges c lam (F.fiber p₀ c₀) v u d, ∀ α,
      IsBoxSmooth 1 1 (fun X z => γ.coeff α s X z) := by
  intro v u d γ hγ α
  have hqs : 1 ≤ qs := by
    have h1 := setting_ambient_output_supported P
    have h2 := P.D_ge
    omega
  have hqf : 1 ≤ qf := by
    have h1 := P.qf_eq
    omega
  rw [← hQe] at hγ
  exact (P.coeff_smooth v u d γ hγ α s hs).mono hqs hqf

include P in
/-- The label lift of a coarse field smooth at the cell time `c⁻¹ t` is `C^D` in the label. -/
theorem setting_labelLift_contDiff {sX sZ : ℕ} (hsZ : 1 ≤ sZ) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (ε : ℝ) (f : ℝ → Vec 2 → ∀ i, h i)
    (ρs es : ℝ) {c t : ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) (f (c⁻¹ * t)))
    (ht : c⁻¹ * t ∈ Set.Icc t₀ t₁) :
    ContDiff ℝ (D : ℕ∞) (labelLift Cc N H ε f ρs es c t) := by
  rw [labelLift_eq_sum_sample]
  exact ContDiff.sum fun hh hhm => CoarseFluxDiff.contDiff_sample
    (setting_liftPolyField_boxD P hsZ hseq (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) ε _ hf
      ht) le_rfl le_rfl ρs es

/-! ### The label edge flux of the label lift -/

include P in
/-- The label edge flux of the label lift is the sum over the grades of the label edge fluxes of
the sampled grades. -/
theorem setting_labelEdgeFlux_labelLift_eq_sum (F : ChartedFamily ι h D Pc Ctx) (ν e E : ℝ)
    (p : Pc) (c₀ : Ctx p) {sX sZ : ℕ} (hsZ : 1 ≤ sZ) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (ε : ℝ) (f : ℝ → Vec 2 → ∀ i, h i)
    (ρs es : ℝ) {c t : ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) (f (c⁻¹ * t)))
    (ht : c⁻¹ * t ∈ Set.Icc t₀ t₁) (τ : ℝ) (v : ι) (y : Vec 2) (i₀ : Fin 2) :
    labelEdgeFlux F ν e E p c₀ τ (labelLift Cc N H ε f ρs es c t) v y i₀ =
      ∑ hh ∈ Finset.range (H + 1), labelEdgeFlux F ν e E p c₀ τ
        (twoScaleSample ρs es (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t))) v y
          i₀ := by
  rw [labelLift_eq_sum_sample]
  exact labelEdgeFlux_finsetSum F ν e E p c₀ τ (Finset.range (H + 1))
    (fun hh => twoScaleSample ρs es (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t)))
    (r := D) (fun hh hhm => CoarseFluxDiff.contDiff_sample
      (setting_liftPolyField_boxD P hsZ hseq (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) ε _
        hf ht) le_rfl le_rfl ρs es)
    (Nat.le_succ D) v y i₀

include P in
/-- The label edge flux of `p₀` of one sampled grade is differentiable in the label. -/
theorem setting_labelEdgeFlux_degree_differentiable (F : ChartedFamily ι h D Pc Ctx)
    (ν e E : ℝ) (p₀ : Pc) (c₀ : Ctx p₀) {c lam : ℝ}
    (hQe : Q.edge = liftEdges c lam (F.fiber p₀ c₀)) (hc : c ≠ 0) (he : e ≠ 0) (hν : ν ≠ 0)
    {ε ρs : ℝ} (hscale : Real.sqrt Q.η * ε = e * ρs⁻¹) (hlam : lam * ρs⁻¹ = E⁻¹) {sX sZ : ℕ}
    (hsZ : 1 ≤ sZ) {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    (f : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) (f (c⁻¹ * t)))
    (ht : c⁻¹ * t ∈ Set.Icc t₀ t₁) {hh : ℕ} (hhh : hh ≤ H) (v : ι) (i₀ : Fin 2) :
    Differentiable ℝ (fun y => labelEdgeFlux F ν e E p₀ c₀ t
      (twoScaleSample ρs e (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t))) v y
        i₀) :=
  labelEdgeFlux_sample_differentiable F ν e E p₀ c₀ he hν hscale hlam (mul_inv_cancel_left₀ hc t)
    (setting_liftedEdge_coeff_box P F p₀ c₀ hQe ht)
    (setting_liftPolyField_boxD P hsZ hseq hhh ε _ hf ht) v i₀

/-! ### The source part as a divergence -/

include P in
/-- **(2) The source part is the label divergence of the label edge flux.** If the source edges
of the setting are the lifted fiber of the piece `p₀` (context `c₀`) with time scale `c`, then
under `√η ε = e/ρs`, `lam ρs⁻¹ = E⁻¹`, `c⁻¹ e (e/ν) = 1`, at a window time (`c⁻¹ t` in the
window) and a label `y`, `c⁻¹` times the source part of `labelRest` (component `v`) is the label
divergence at `y` of the label edge flux of `p₀` at the physical time `t` applied to the full
label lift `V = labelLift …`. -/
theorem source_part_label_div (F : ChartedFamily ι h D Pc Ctx) (ν e E : ℝ) (p₀ : Pc)
    (c₀ : Ctx p₀) {c lam : ℝ} (hQe : Q.edge = liftEdges c lam (F.fiber p₀ c₀)) (hc : c ≠ 0)
    (he : e ≠ 0) (hν : ν ≠ 0) {ε ρs : ℝ} (hscale : Real.sqrt Q.η * ε = e * ρs⁻¹)
    (hlam : lam * ρs⁻¹ = E⁻¹) (hsc : c⁻¹ * (e * (e / ν)) = 1) {sX sZ : ℕ} (hsZ : 1 ≤ sZ)
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    (f : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) (f (c⁻¹ * t)))
    (ht : c⁻¹ * t ∈ Set.Icc t₀ t₁) (y : Vec 2) (v : ι) :
    c⁻¹ • labelSourcePart Q Cc N H ε f ρs e c t y v =
      ∑ i₀ : Fin 2, fderiv ℝ (fun y' => labelEdgeFlux F ν e E p₀ c₀ t
        (labelLift Cc N H ε f ρs e c t) v y' i₀) y (basisVec i₀) := by
  have hdeg : ∀ hh ∈ Finset.range (H + 1), c⁻¹ • sourceOp Q.edge Q.η ε (c⁻¹ * t)
      (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t)) (ρs⁻¹ • y) (e⁻¹ • y) v =
      ∑ i₀ : Fin 2, fderiv ℝ (fun y' => labelEdgeFlux F ν e E p₀ c₀ t
        (twoScaleSample ρs e (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t))) v y'
          i₀) y (basisVec i₀) := by
    intro hh hhm
    have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
    rw [hQe, sourceOp_lift_apply_eq_labelDiv F ν e E p₀ c₀ he hν hscale hlam
      (mul_inv_cancel_left₀ hc t) (setting_liftedEdge_coeff_box P F p₀ c₀ hQe ht)
      (setting_liftPolyField_boxD P hsZ hseq hhh ε _ hf ht) y v, smul_smul, hsc, one_smul]
  have hR : ∀ i₀ : Fin 2, fderiv ℝ (fun y' => labelEdgeFlux F ν e E p₀ c₀ t
      (labelLift Cc N H ε f ρs e c t) v y' i₀) y (basisVec i₀) =
      ∑ hh ∈ Finset.range (H + 1), fderiv ℝ (fun y' => labelEdgeFlux F ν e E p₀ c₀ t
        (twoScaleSample ρs e (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t))) v y'
          i₀) y (basisVec i₀) := by
    intro i₀
    have hfun : (fun y' => labelEdgeFlux F ν e E p₀ c₀ t (labelLift Cc N H ε f ρs e c t) v y'
        i₀) = fun y' => ∑ hh ∈ Finset.range (H + 1), labelEdgeFlux F ν e E p₀ c₀ t
          (twoScaleSample ρs e (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t))) v y'
            i₀ :=
      funext fun y' => setting_labelEdgeFlux_labelLift_eq_sum P F ν e E p₀ c₀ hsZ hseq ε f ρs e
        hf ht t v y' i₀
    have hd : ∀ hh ∈ Finset.range (H + 1), DifferentiableAt ℝ (fun y' =>
        labelEdgeFlux F ν e E p₀ c₀ t
          (twoScaleSample ρs e (liftPolyField Cc N ε hh (fun _ => f (c⁻¹ * t)) (c⁻¹ * t))) v y'
            i₀) y := fun hh hhm =>
      setting_labelEdgeFlux_degree_differentiable P F ν e E p₀ c₀ hQe hc he hν hscale hlam hsZ
        hseq f hf ht (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) v i₀ y
    rw [hfun, fderiv_fun_sum hd]
    simp only [FunLike.coe_sum, Finset.sum_apply]
  rw [labelSourcePart, source_part_top_vanish P hsZ hseq ε (f (c⁻¹ * t)) ht (ρs⁻¹ • y) (e⁻¹ • y),
    Finset.sum_apply, Finset.smul_sum, Finset.sum_congr rfl hdeg, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i₀ _ => (hR i₀).symm

end Setting

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift
open scoped Matrix
namespace AVRegularity.CycleComparison.Reconstruction

/-! **At quiet times the pulse means are physical operators**.

At a quiet cell time (`IsQuietOn`: no drift, fast independent source coefficients) the means of
the lifts are explicit (`cycle_residual_quiet_mean`):
`L_2^{(0)} = ℬ₂ I`, `L_n^{(1)} = -𝒮_n I`, every other mean vanishes. Read in the chart `χ` of a
pulse (unit Jacobian, labels `ψ = χ⁻¹`, metric `G(s, ρ⁻¹y) = Dχ(y)⁻¹ Dχ(y)⁻ᵀ`) on the chart-frame
field `A(X) = a(χ(ρX))` of a smooth physical field `a`, these are pulse-independent physical
operators:

* `cellB2_chart`: `ℬ₂ A` at the label `ρ⁻¹ ψ x` is `-η ρ² Δa(x)` (`sample_div_metric` for the fast
  independent field, whose fast derivatives vanish, and `chart_laplacian`);
* `quiet_mean_zero`: `c⁻¹ ∑_{n=2}^{N+D} ε_c^n L_n^{(0)} A = -ν Δa` when `ε_c² η = c ν ρ⁻²`;
* `quiet_mean_high`: the means of the grades `2 ≤ r ≤ H` vanish;
* `quiet_source_polynomial`: at a quiet time the source `𝒮_ε A` of a coarse field is the
  polynomial `∑_{d=2}^{D} ε^d √η ∂_X·(flux_d)` (`sourceOp_independent_expand`; the fast
  divergences vanish), so its Taylor coefficients `𝒮_n`, `2 ≤ n ≤ N + D`, sum back to it;
* `quiet_mean_one`: `c⁻¹ ∑ ε_c^n L_n^{(1)} A` is minus the physical divergence of the family edge
  flux of `a`, as soon as that flux is the Piola transport of the label edge flux of `a ∘ χ`
  (`sourceOp_lift_apply_eq_labelDiv`, `div_eq_label_div_of_transported`); this applies at a
  single-piece time and on a quiet overlap;
* `pulseMeanField_quiet_zero`, `pulseMeanField_quiet_one`, `pulseMeanField_quiet_high`: the same
  for `pulseMeanField`, whose time-dependent input is `A` at the cell time `c⁻¹ t`
  (`pulseMeanField_eq_frame`, by `liftMean_congr_time_input`).
-/

/-! ### `ℬ₂` of a chart-frame field -/

section Diffusion

/-- **The sampled divergence form of a fast independent field** is its slow-slow part:
`div_y(G(ρ⁻¹y) ∇_y SΦ)(y) = ρ⁻² ∑_{ij} ∂_{X_i}(G_{ij} ∂_{X_j}Φ)(ρ⁻¹y, e⁻¹y)`. -/
theorem sample_div_metric_fastIndep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : Vec 2 → Vec 2 → E} (hΦ : IsBoxSmooth 2 2 Φ) (hfi : FastIndep Φ)
    (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (hG : ∀ i j, Differentiable ℝ (fun X => G X i j))
    (ρ e : ℝ) (y : Vec 2) :
    ∑ i, fderiv ℝ (fun y' => ∑ j, G (ρ⁻¹ • y') i j •
        fderiv ℝ (twoScaleSample ρ e Φ) y' (basisVec j)) y (basisVec i) =
      (ρ⁻¹ * ρ⁻¹) • ∑ i, ∑ j,
        slowPartial i (fun X' z' => G X' i j • slowPartial j Φ X' z') (ρ⁻¹ • y) (e⁻¹ • y) := by
  have hFF : ∀ i j X z, fastPartial i (fastPartial j Φ) X z = 0 := by
    intro i j X z
    have hj : FastIndep (fastPartial j Φ) := fun X' z₁ z₂ => by
      rw [hfi.fastPartial j X' z₁, hfi.fastPartial j X' z₂]
    exact hj.fastPartial i X z
  have hFS : ∀ i j X z, fastPartial i (slowPartial j Φ) X z = 0 := by
    intro i j X z
    have hj : FastIndep (slowPartial j Φ) := fun X' z₁ z₂ => hfi.slowPartial j X' z₁ z₂
    exact hj.fastPartial i X z
  have hSF : ∀ i j X z,
      slowPartial i (fun X' z' => G X' i j • fastPartial j Φ X' z') X z = 0 := by
    intro i j X z
    have h0 : (fun X' z' => G X' i j • fastPartial j Φ X' z') = fun _ _ => (0 : E) :=
      funext fun X' => funext fun z' => by
        show G X' i j • fastPartial j Φ X' z' = 0
        rw [hfi.fastPartial j X' z', smul_zero]
    rw [h0]
    simp [slowPartial]
  rw [sample_div_metric hΦ G hG ρ e y]
  simp only [hFF, hFS, hSF, smul_zero, add_zero, Finset.sum_const_zero, zero_add]

/-- **`ℬ₂` of a chart-frame field is the physical Laplacian.** For a chart `χ` of unit
Jacobian with labels `ψ = χ⁻¹`, a slow metric with `G(s, ρ⁻¹y) = Dχ(y)⁻¹ Dχ(y)⁻ᵀ` and the
chart-frame field `A(X) = a(χ(ρX))` of a smooth physical field `a`,
`ℬ₂ A(ρ⁻¹ψ x, z) = -η ρ² Δa(x)`. -/
theorem cellB2_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (s : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) {χ ψ : Vec 2 → Vec 2}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : Differentiable ℝ ψ) (hψχ : ∀ y, ψ (χ y) = y)
    (hχψ : ∀ x, χ (ψ x) = x) (hd : ∀ y, (jacMatrix χ y).det = 1)
    (hG : ∀ y, (fun i j => G s (ρ⁻¹ • y) i j) = (jacMatrix χ y)⁻¹ * ((jacMatrix χ y)⁻¹)ᵀ)
    (hGd : ∀ i j, Differentiable ℝ (fun X => G s X i j)) {a : Vec 2 → E}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (x z : Vec 2) :
    cellB2 η G s (fun X' _ => a (χ (ρ • X'))) (ρ⁻¹ • ψ x) z =
      -(η * ρ * ρ) • ∑ k, fderiv ℝ (fun x' => fderiv ℝ a x' (basisVec k)) x (basisVec k) := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun X' : Vec 2 => a (χ (ρ • X'))) :=
    ha.comp (hχ.comp (contDiff_const_smul ρ))
  have hΦ : IsBoxSmooth 2 2 (fun (X' : Vec 2) (_ : Vec 2) => a (χ (ρ • X'))) :=
    isBoxSmooth_slow_field 2 2 _ (hA.of_le (by exact_mod_cast le_top))
  have hfi : FastIndep (fun (X' : Vec 2) (_ : Vec 2) => a (χ (ρ • X'))) := fun _ _ _ => rfl
  have hsample : twoScaleSample ρ 1 (fun (X' : Vec 2) (_ : Vec 2) => a (χ (ρ • X'))) =
      fun y => a (χ y) := by
    funext y
    show a (χ (ρ • ρ⁻¹ • y)) = a (χ y)
    rw [smul_smul, mul_inv_cancel₀ hρ, one_smul]
  have hsm : Differentiable ℝ (fun y' : Vec 2 => ρ⁻¹ • y') := by fun_prop
  have hGd' : ∀ i j, Differentiable ℝ (fun y : Vec 2 => G s (ρ⁻¹ • y) i j) := fun i j =>
    (hGd i j).comp hsm
  have hV : ContDiff ℝ 2 (fun y => a (χ y)) := (ha.comp hχ).of_le (by simp)
  have hlap : ∑ k, fderiv ℝ (fun x' => fderiv ℝ a x' (basisVec k)) x (basisVec k) =
      ∑ i, fderiv ℝ (fun y => ∑ j, G s (ρ⁻¹ • y) i j •
        fderiv ℝ (fun y' => a (χ y')) y (basisVec j)) (ψ x) (basisVec i) := by
    have h := chart_laplacian hχ hψ hψχ hχψ hd (fun y => fun i j => G s (ρ⁻¹ • y) i j) hG hGd'
      hV x
    have hfun : (fun x'' => a (χ (ψ x''))) = a := funext fun x'' => congrArg a (hχψ x'')
    rw [hfun] at h
    exact h
  have hSS := sample_div_metric_fastIndep hΦ hfi (G s) hGd ρ 1 (ψ x)
  rw [hsample] at hSS
  have hc : -(η * ρ * ρ) * (ρ⁻¹ * ρ⁻¹) = -η := by
    have hρρ : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
    linear_combination (-η * (ρ * ρ⁻¹) - η) * hρρ
  rw [FastIndep.cellB2 η G s hfi (ρ⁻¹ • ψ x) z ((1 : ℝ)⁻¹ • ψ x), hlap, hSS, smul_smul, hc,
    neg_smul]
  rfl

end Diffusion

/-! ### The source of a coarse field at a quiet time -/

section QuietSource

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- At a time where the source coefficients are fast independent, the source flux of a coarse
field of each covariant order is fast independent. -/
theorem slowSourceFluxOrder_fastIndep (edge : ConstituentEdges D h) (η s : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α s X z = γ.coeff α s X z')
    (A : Vec 2 → ∀ i, h i) (d : Finset.Icc 2 D) (q : Fin 2) :
    FastIndep (slowSourceFluxOrder edge η s A d q) := fun X z z' => by
  funext v
  simp only [slowSourceFluxOrder]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  refine List.map_congr_left fun γ hγ => ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hquiet v u d γ hγ α X z z']

/-- The coefficient of `ε^n` of the source of a coarse field `A` at a quiet time: the slow
divergence `√η ∑_q ∂_{X_q}(flux_n)_q` of the source flux of covariant order `n` for
`2 ≤ n ≤ D`, and zero otherwise. -/
def quietSourceTerm (edge : ConstituentEdges D h) (η s : ℝ) (A : Vec 2 → ∀ i, h i) (n : ℕ)
    (X z : Vec 2) : ∀ i, h i :=
  if hn : n ∈ Finset.Icc 2 D then
    Real.sqrt η • ∑ q : Fin 2, slowPartial q (slowSourceFluxOrder edge η s A ⟨n, hn⟩ q) X z
  else 0

/-- `quietSourceTerm` at an order `2 ≤ d ≤ D`. -/
theorem quietSourceTerm_coe (edge : ConstituentEdges D h) (η s : ℝ) (A : Vec 2 → ∀ i, h i)
    (d : Finset.Icc 2 D) (X z : Vec 2) :
    quietSourceTerm edge η s A d.1 X z =
      Real.sqrt η • ∑ q : Fin 2, slowPartial q (slowSourceFluxOrder edge η s A d q) X z :=
  dite_eq_left d.2

/-- `quietSourceTerm` vanishes outside the orders `2 ≤ n ≤ D`. -/
theorem quietSourceTerm_of_notMem (edge : ConstituentEdges D h) (η s : ℝ)
    (A : Vec 2 → ∀ i, h i) {n : ℕ} (hn : n ∉ Finset.Icc 2 D) (X z : Vec 2) :
    quietSourceTerm edge η s A n X z = 0 :=
  dite_eq_right hn

/-- A sum of the terms `ε^n T_n` over a set of degrees containing `[2, D]` is the sum over
`[2, D]`. -/
theorem sum_quietSourceTerm_of_subset (edge : ConstituentEdges D h) (η s : ℝ)
    (A : Vec 2 → ∀ i, h i) {T : Finset ℕ} (hT : Finset.Icc 2 D ⊆ T) (ε : ℝ) (X z : Vec 2) :
    ∑ n ∈ T, ε ^ n • quietSourceTerm edge η s A n X z =
      ∑ n ∈ Finset.Icc 2 D, ε ^ n • quietSourceTerm edge η s A n X z := by
  refine (Finset.sum_subset hT fun n _ hn => ?_).symm
  rw [quietSourceTerm_of_notMem edge η s A hn X z, smul_zero]

/-- The degrees `[2, D]` lie in `[0, D]`. -/
theorem Icc_two_subset_range (D : ℕ) : Finset.Icc 2 D ⊆ Finset.range (D + 1) := fun _ hn =>
  Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hn).2)

/-- **At a quiet time the source of a coarse field is a polynomial in `ε` of degree `≤ D` without
constant and linear terms**: `𝒮_ε A = ∑_{n ≤ D} ε^n T_n` with `T_n = quietSourceTerm … n`. -/
theorem sourceOp_quiet_eq_poly (edge : ConstituentEdges D h) (η s : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α s X z = γ.coeff α s X z')
    (hslow : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z, ContDiff ℝ 1 (fun X => γ.coeff α s X z))
    {A : Vec 2 → ∀ i, h i} (hA : ContDiff ℝ (D : ℕ∞) A) (ε : ℝ) (X z : Vec 2) :
    sourceOp edge η ε s (fun X' _ => A X') X z =
      ∑ n ∈ Finset.range (D + 1), ε ^ n • quietSourceTerm edge η s A n X z := by
  have hfast : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X', ContDiff ℝ 1 (γ.coeff α s X') := by
    intro v u d γ hγ α X'
    have hc : γ.coeff α s X' = fun _ => γ.coeff α s X' 0 :=
      funext fun z' => hquiet v u d γ hγ α X' z' 0
    rw [hc]
    exact contDiff_const
  have hF0 : ∀ (d : Finset.Icc 2 D) (q : Fin 2),
      fastPartial q (slowSourceFluxOrder edge η s A d q) X z = 0 := fun d q =>
    (slowSourceFluxOrder_fastIndep edge η s hquiet A d q).fastPartial q X z
  have hcoe : ∑ d : Finset.Icc 2 D, ε ^ d.1 • quietSourceTerm edge η s A d.1 X z =
      ∑ n ∈ Finset.Icc 2 D, ε ^ n • quietSourceTerm edge η s A n X z :=
    Finset.sum_coe_sort (Finset.Icc 2 D) (fun n => ε ^ n • quietSourceTerm edge η s A n X z)
  rw [sourceOp_independent_expand edge η ε s A hA hfast hslow X z,
    sum_quietSourceTerm_of_subset edge η s A (Icc_two_subset_range D) ε X z, ← hcoe]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [quietSourceTerm_coe edge η s A d X z, Finset.sum_eq_zero fun q _ => hF0 d q, smul_zero,
    zero_add]

/-- At a quiet time the Taylor coefficients `𝒮_n A` of the source of a coarse field are the
coefficients `quietSourceTerm … n` of the source polynomial. -/
theorem sourceCoeff_quiet (edge : ConstituentEdges D h) (η s : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α s X z = γ.coeff α s X z')
    (hslow : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z, ContDiff ℝ 1 (fun X => γ.coeff α s X z))
    {A : Vec 2 → ∀ i, h i} (hA : ContDiff ℝ (D : ℕ∞) A) (n : ℕ) (X z : Vec 2) :
    sourceCoeff edge η n s (fun X' _ => A X') X z = quietSourceTerm edge η s A n X z := by
  have hfun : (fun ε : ℝ => sourceOp edge η ε s (fun X' _ => A X') X z) =
      fun ε => ∑ i ∈ Finset.range (D + 1), ε ^ i • quietSourceTerm edge η s A i X z :=
    funext fun ε => sourceOp_quiet_eq_poly edge η s hquiet hslow hA ε X z
  simp only [sourceCoeff, hfun, iteratedDeriv_epsPoly]
  by_cases hn : n ≤ D
  · simp [hn, Nat.factorial_ne_zero]
  · rw [quietSourceTerm_of_notMem edge η s A (fun hm => hn (Finset.mem_Icc.1 hm).2) X z]
    simp [hn]

/-- **The quiet source is the sum of its Taylor coefficients over `2 ≤ n ≤ N + D`.** At a
time where the source coefficients are fast independent (and `C¹` in the slow variable), for a
`C^D` coarse field `A`, `∑_{n=2}^{N+D} ε^n 𝒮_n A = 𝒮_ε A`: the source polynomial has only the
degrees `2 ≤ d ≤ D ≤ N + D` (its fast divergences vanish). -/
theorem quiet_source_polynomial (edge : ConstituentEdges D h) (η s : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α s X z = γ.coeff α s X z')
    (hslow : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z, ContDiff ℝ 1 (fun X => γ.coeff α s X z))
    {A : Vec 2 → ∀ i, h i} (hA : ContDiff ℝ (D : ℕ∞) A) (N : ℕ) (ε : ℝ) (X z : Vec 2) :
    ∑ n ∈ Finset.Icc 2 (N + D), ε ^ n • sourceCoeff edge η n s (fun X' _ => A X') X z =
      sourceOp edge η ε s (fun X' _ => A X') X z := by
  rw [sourceOp_quiet_eq_poly edge η s hquiet hslow hA ε X z,
    sum_quietSourceTerm_of_subset edge η s A (Icc_two_subset_range D) ε X z,
    ← sum_quietSourceTerm_of_subset edge η s A
      (Finset.Icc_subset_Icc_right (Nat.le_add_left D N)) ε X z]
  exact Finset.sum_congr rfl fun n _ => by rw [sourceCoeff_quiet edge η s hquiet hslow hA n X z]

end QuietSource

/-! ### The time-dependent input of `pulseMeanField` -/

section PulseMean

/-- `pulseMeanField` at the time `t` reads its input at the cell time `c⁻¹ t`, where it is the
chart-frame field `X ↦ a(t, χ_t(ρX))`. -/
theorem pulseMeanField_eq_frame {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (c ρ εc : ℝ) (N r : ℕ)
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (hc : c ≠ 0)
    (x : Vec 2) :
    pulseMeanField c ρ εc N r Q Cc chart label a t x =
      c⁻¹ • ∑ n ∈ Finset.Icc 2 (N + D), εc ^ n •
        liftMean Q Cc (fun _ => fun X => a t (chart t (ρ • X))) r n (c⁻¹ * t)
          (ρ⁻¹ • label t x) := by
  have hin : (fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) (c⁻¹ * t) =
      (fun (_ : ℝ) (X : Vec 2) => a t (chart t (ρ • X))) (c⁻¹ * t) := by
    funext X
    show a (c * (c⁻¹ * t)) (chart (c * (c⁻¹ * t)) (ρ • X)) = a t (chart t (ρ • X))
    rw [mul_inv_cancel_left₀ hc t]
  rw [pulseMeanField]
  refine congrArg (c⁻¹ • ·) (Finset.sum_congr rfl fun n _ => ?_)
  rw [liftMean_congr_time_input Q Cc (fun s' X' => a (c * s') (chart (c * s') (ρ • X')))
    (fun _ X => a t (chart t (ρ • X))) r n (c⁻¹ * t) hin]

end PulseMean

/-! ### The quiet means in the setting -/

section Setting

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K₀ k₀ L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {t₀ t₁ e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : Fin 2} {Vsh : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bE : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π t₀ t₁ e₀ ν₀ B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ par Vsh H N K₀ k₀ L qs qf CG
    Cw Cj bE Θ)
  {Pc : Type*} {Ctx : Pc → Type*}

include P in
/-- **The quiet mean in the setting** (`cycle_residual_quiet_mean`): at a
quiet time the mean of grade `hh ≤ H` and degree `2 ≤ n ≤ N + D` of a smooth coarse field `A` is
`ℬ₂ A` for `(hh, n) = (0, 2)`, `-𝒮_n A` for `hh = 1`, and zero otherwise. -/
theorem setting_quiet_mean (hDsZ : D ≤ max (k₀ + 1) (L + 2)) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q (K₀ + D + 2) (max (k₀ + 1) (L + 2)) t₀ t₁ N H Cc) {S : Set ℝ}
    (hS : S ⊆ Set.Icc t₀ t₁) (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {A : Vec 2 → ∀ i, h i} (hA : ContDiff ℝ (⊤ : ℕ∞) A) {hh : ℕ} (hhH : hh ≤ H) {n : ℕ}
    (hn2 : 2 ≤ n) (hnND : n ≤ N + D) {s : ℝ} (hs : s ∈ S) (X : Vec 2) :
    liftMean Q Cc (fun _ => A) hh n s X =
      if hh = 0 then (if n = 2 then cellB2 Q.η Q.G s (fun X' _ => A X') X 0 else 0)
      else if hh = 1 then -sourceCoeff Q.edge Q.η n s (fun X' _ => A X') X 0
      else 0 :=
  AVRegularity.Providers.cycle_residual_quiet_mean N K₀ k₀ L D H CG Cw Cj hDsZ Q π t₀ t₁ e₀ ν₀
    B₀ ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ par Vsh qs qf bE Θ P Cc hseq S hS hq A hA hh hhH n hn2 hnND s hs X

include P in
/-- **The quiet diagonal mean is the physical diffusion.** At a quiet cell time `s`, for a
chart `χ` of unit Jacobian with labels `ψ`, a lift metric of the pulse shape
`G(s, ρ⁻¹y) = Dχ(y)⁻¹ Dχ(y)⁻ᵀ` and the scale identity `ε_c² η = c ν ρ⁻²`, the grade-zero mean of
the chart-frame field `A(X) = a(χ(ρX))` at the label `ρ⁻¹ψ x` is `-ν Δa(x)`. -/
theorem quiet_mean_zero (hDsZ : D ≤ max (k₀ + 1) (L + 2)) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q (K₀ + D + 2) (max (k₀ + 1) (L + 2)) t₀ t₁ N H Cc) {S : Set ℝ}
    (hS : S ⊆ Set.Icc t₀ t₁) (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {s : ℝ} (hs : s ∈ S) {c ν ρ εc : ℝ} (hc : c ≠ 0) (hρ : ρ ≠ 0)
    (hscale : εc ^ 2 * Q.η = c * ν * ρ⁻¹ * ρ⁻¹) {χ ψ : Vec 2 → Vec 2}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : Differentiable ℝ ψ) (hψχ : ∀ y, ψ (χ y) = y)
    (hχψ : ∀ x, χ (ψ x) = x) (hd : ∀ y, (jacMatrix χ y).det = 1)
    (hG : ∀ y, (fun i j => Q.G s (ρ⁻¹ • y) i j) = (jacMatrix χ y)⁻¹ * ((jacMatrix χ y)⁻¹)ᵀ)
    {a : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (x : Vec 2) :
    c⁻¹ • ∑ n ∈ Finset.Icc 2 (N + D), εc ^ n •
        liftMean Q Cc (fun _ => fun X => a (χ (ρ • X))) 0 n s (ρ⁻¹ • ψ x) =
      -ν • ∑ k, fderiv ℝ (fun x' => fderiv ℝ a x' (basisVec k)) x (basisVec k) := by
  have hsI : s ∈ Set.Icc t₀ t₁ := hS hs
  have hqs1 : 1 ≤ qs := by
    have h1 := setting_ambient_output_supported P
    have h2 := P.D_ge
    omega
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun X : Vec 2 => a (χ (ρ • X))) :=
    ha.comp (hχ.comp (contDiff_const_smul ρ))
  have h2mem : 2 ∈ Finset.Icc 2 (N + D) :=
    Finset.mem_Icc.2 ⟨le_rfl, by have := P.D_ge; omega⟩
  have hmean : ∀ n ∈ Finset.Icc 2 (N + D),
      liftMean Q Cc (fun _ => fun X => a (χ (ρ • X))) 0 n s (ρ⁻¹ • ψ x) =
        if n = 2 then cellB2 Q.η Q.G s (fun X' _ => a (χ (ρ • X'))) (ρ⁻¹ • ψ x) 0 else 0 :=
    fun n hn => (setting_quiet_mean P hDsZ hseq hS hq hA (Nat.zero_le H)
      (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2 hs (ρ⁻¹ • ψ x)).trans (ite_eq_left rfl)
  have hGd : ∀ i j, Differentiable ℝ (fun X => Q.G s X i j) := fun i j => by
    have h1 : ContDiff ℝ 1 (fun X => Q.G s X i j) :=
      (P.G_smooth s hsI i j).of_le (by exact_mod_cast hqs1)
    exact h1.differentiable one_ne_zero
  have hcoef : c⁻¹ * εc ^ 2 * -(Q.η * ρ * ρ) = -ν := by
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
    have hρρ : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
    linear_combination (-c⁻¹ * ρ * ρ) * hscale + (-ν) * hcc +
      (-ν * (c * c⁻¹) * (1 + ρ * ρ⁻¹)) * hρρ
  rw [Finset.sum_eq_single_of_mem 2 h2mem, hmean 2 h2mem, ite_eq_left rfl,
    cellB2_chart Q.η Q.G s hρ hχ hψ hψχ hχψ hd hG hGd ha x 0, smul_smul, smul_smul, hcoef]
  intro n hn hn2
  rw [hmean n hn, ite_eq_right hn2, smul_zero]

include P in
/-- **The quiet means of the grades `2 ≤ r ≤ H` vanish.** -/
theorem quiet_mean_high (hDsZ : D ≤ max (k₀ + 1) (L + 2)) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q (K₀ + D + 2) (max (k₀ + 1) (L + 2)) t₀ t₁ N H Cc) {S : Set ℝ}
    (hS : S ⊆ Set.Icc t₀ t₁) (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {s : ℝ} (hs : s ∈ S) {r : ℕ} (hr : 2 ≤ r) (hrH : r ≤ H) {A : Vec 2 → ∀ i, h i}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (c εc : ℝ) (X : Vec 2) :
    c⁻¹ • ∑ n ∈ Finset.Icc 2 (N + D), εc ^ n • liftMean Q Cc (fun _ => A) r n s X = 0 := by
  have hr0 : r ≠ 0 := by omega
  have hr1 : r ≠ 1 := by omega
  have hz : ∀ n ∈ Finset.Icc 2 (N + D), εc ^ n • liftMean Q Cc (fun _ => A) r n s X = 0 := by
    intro n hn
    rw [setting_quiet_mean P hDsZ hseq hS hq hA hrH (Finset.mem_Icc.1 hn).1
      (Finset.mem_Icc.1 hn).2 hs X, ite_eq_right hr0, ite_eq_right hr1, smul_zero]
  rw [Finset.sum_eq_zero hz, smul_zero]

include P in
/-- **The quiet source mean is minus the source.** At a quiet cell time, for `1 ≤ H` and a smooth
coarse field `A`, `∑_{n=2}^{N+D} ε^n L_n^{(1)} A = -𝒮_ε A` (at any fast point `z`: both sides are
fast independent). -/
theorem quiet_mean_one_source (hDsZ : D ≤ max (k₀ + 1) (L + 2)) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q (K₀ + D + 2) (max (k₀ + 1) (L + 2)) t₀ t₁ N H Cc) {S : Set ℝ}
    (hS : S ⊆ Set.Icc t₀ t₁) (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {s : ℝ} (hs : s ∈ S) (hH : 1 ≤ H) {A : Vec 2 → ∀ i, h i} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (ε : ℝ) (X z : Vec 2) :
    ∑ n ∈ Finset.Icc 2 (N + D), ε ^ n • liftMean Q Cc (fun _ => A) 1 n s X =
      -sourceOp Q.edge Q.η ε s (fun X' _ => A X') X z := by
  have hsI : s ∈ Set.Icc t₀ t₁ := hS hs
  have hqs1 : 1 ≤ qs := by
    have h1 := setting_ambient_output_supported P
    have h2 := P.D_ge
    omega
  have hquiet : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X' z₁ z₂,
      γ.coeff α s X' z₁ = γ.coeff α s X' z₂ :=
    fun v u d γ hγ α X' z₁ z₂ => hq.2 v u d γ hγ α s hs X' z₁ z₂
  have hslow : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z, ContDiff ℝ 1 (fun X => γ.coeff α s X z) :=
    fun v u d γ hγ α z' =>
      ((P.coeff_smooth v u d γ hγ α s hsI).contDiff_slow z').of_le (by exact_mod_cast hqs1)
  have hfi : FastIndep (fun (X' : Vec 2) (_ : Vec 2) => A X') := fun _ _ _ => rfl
  have h10 : (1 : ℕ) ≠ 0 := one_ne_zero
  have hmean : ∀ n ∈ Finset.Icc 2 (N + D), ε ^ n • liftMean Q Cc (fun _ => A) 1 n s X =
      -(ε ^ n • sourceCoeff Q.edge Q.η n s (fun X' _ => A X') X z) := by
    intro n hn
    rw [setting_quiet_mean P hDsZ hseq hS hq hA hH (Finset.mem_Icc.1 hn).1
      (Finset.mem_Icc.1 hn).2 hs X, ite_eq_right h10, ite_eq_left rfl, smul_neg,
      sourceCoeff_fastIndep Q.edge Q.η s n hquiet hfi X 0 z]
  rw [Finset.sum_congr rfl hmean, Finset.sum_neg_distrib,
    quiet_source_polynomial Q.edge Q.η s hquiet hslow (hA.of_le (by exact_mod_cast le_top)) N ε
      X z]

include P in
/-- **The quiet source mean is minus the physical divergence of the edge flux.** Let the
source edges of the setting be the lifted fiber of the piece `p₀` (time scale `c`), with the
scale laws `√η ε_c = e/ρ_s`, `lam ρ_s⁻¹ = E⁻¹`, `c⁻¹ e (e/ν) = 1`, let `c⁻¹ t` be a quiet cell
time and `1 ≤ H`. Let `χ` be a chart of unit Jacobian with labels `ψ` and `a` a smooth physical
field such that the family edge flux of `a` at the time `t` is the Piola transport of the label
edge flux of `p₀` applied to `a ∘ χ` (`hflux`). Then `c⁻¹` times the grade-one mean of the
chart-frame field `A(X) = a(χ(ρ_s X))` at the label `ρ_s⁻¹ψ x` (component `v`) is minus the
physical divergence of that family edge flux at `x`. -/
theorem quiet_mean_one (F : ChartedFamily ι h D Pc Ctx) (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (K : ι → ℕ) (p₀ : Pc) {c lam : ℝ}
    (hQe : Q.edge = liftEdges c lam (F.fiber p₀ (actual p₀))) (hc : c ≠ 0) (he : e ≠ 0)
    (hν : ν ≠ 0) {εc ρs : ℝ} (hρs : ρs ≠ 0) (hscale : Real.sqrt Q.η * εc = e * ρs⁻¹)
    (hlam : lam * ρs⁻¹ = E⁻¹) (hsc : c⁻¹ * (e * (e / ν)) = 1)
    (hDsZ : D ≤ max (k₀ + 1) (L + 2)) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q (K₀ + D + 2) (max (k₀ + 1) (L + 2)) t₀ t₁ N H Cc) (hH : 1 ≤ H)
    {S : Set ℝ} (hS : S ⊆ Set.Icc t₀ t₁)
    (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S) {t : ℝ} (ht : c⁻¹ * t ∈ S)
    {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (hd : ∀ y, (jacMatrix χ y).det = 1)
    {a : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (v : ι)
    (hflux : ∀ x' (a₀ : Fin 2), ∑ i' : ι, ∑ d : admissibleOrders K D v i',
        edgeCoefficient F ν e E actual K v i' d t x'
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => a y i') x') a₀ =
      ∑ i₀ : Fin 2, chartInvJacobian ψ x' a₀ i₀ •
        labelEdgeFlux F ν e E p₀ (actual p₀) t (fun y => a (χ y)) v (ψ x') i₀)
    (x : Vec 2) :
    (c⁻¹ • ∑ n ∈ Finset.Icc 2 (N + D), εc ^ n •
        liftMean Q Cc (fun _ => fun X => a (χ (ρs • X))) 1 n (c⁻¹ * t) (ρs⁻¹ • ψ x)) v =
      -∑ a₀ : Fin 2, fderiv ℝ (fun x' => ∑ i' : ι, ∑ d : admissibleOrders K D v i',
        edgeCoefficient F ν e E actual K v i' d t x'
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => a y i') x') a₀) x (basisVec a₀) := by
  have hsI : c⁻¹ * t ∈ Set.Icc t₀ t₁ := hS ht
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun X : Vec 2 => a (χ (ρs • X))) :=
    ha.comp (hχ.comp (contDiff_const_smul ρs))
  have hΦD : IsBoxSmooth D D (fun (X' : Vec 2) (_ : Vec 2) => a (χ (ρs • X'))) :=
    isBoxSmooth_slow_field D D _ (hA.of_le (by exact_mod_cast le_top))
  have hΓ := setting_liftedEdge_coeff_box P F p₀ (actual p₀) hQe hsI
  have hsample : twoScaleSample ρs e (fun (X' : Vec 2) (_ : Vec 2) => a (χ (ρs • X'))) =
      fun y => a (χ y) := by
    funext y
    show a (χ (ρs • ρs⁻¹ • y)) = a (χ y)
    rw [smul_smul, mul_inv_cancel₀ hρs, one_smul]
  have hGd : ∀ l : Fin 2, Differentiable ℝ
      (fun y => labelEdgeFlux F ν e E p₀ (actual p₀) t (fun y' => a (χ y')) v y l) := by
    intro l
    have h1 := labelEdgeFlux_sample_differentiable F ν e E p₀ (actual p₀) he hν hscale hlam
      (mul_inv_cancel_left₀ hc t) hΓ hΦD v l
    rw [hsample] at h1
    exact h1
  have hstep : (c⁻¹ • ∑ n ∈ Finset.Icc 2 (N + D), εc ^ n •
        liftMean Q Cc (fun _ => fun X => a (χ (ρs • X))) 1 n (c⁻¹ * t) (ρs⁻¹ • ψ x)) v =
      -∑ i₀ : Fin 2, fderiv ℝ (fun y => labelEdgeFlux F ν e E p₀ (actual p₀) t
        (fun y' => a (χ y')) v y i₀) (ψ x) (basisVec i₀) := by
    rw [Pi.smul_apply, quiet_mean_one_source P hDsZ hseq hS hq ht hH hA εc (ρs⁻¹ • ψ x)
      (e⁻¹ • ψ x), Pi.neg_apply, smul_neg, hQe, sourceOp_lift_apply_eq_labelDiv F ν e E p₀
      (actual p₀) he hν hscale hlam (mul_inv_cancel_left₀ hc t) hΓ hΦD (ψ x) v, smul_smul, hsc,
      one_smul, hsample]
  exact hstep.trans (congrArg Neg.neg (div_eq_label_div_of_transported hχ hψ hψχ hχψ hd
    (G := fun y i₀ => labelEdgeFlux F ν e E p₀ (actual p₀) t (fun y' => a (χ y')) v y i₀)
    hGd hflux x).symm)

/-! ### `pulseMeanField` at quiet times -/

include P in
/-- **The diagonal pulse mean at a quiet time is `-ν Δa`** (hypotheses of `quiet_mean_zero`
for the chart `chart t` with labels `label t` at the cell time `c⁻¹ t`). -/
theorem pulseMeanField_quiet_zero (hDsZ : D ≤ max (k₀ + 1) (L + 2))
    {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q (K₀ + D + 2) (max (k₀ + 1) (L + 2)) t₀ t₁ N H Cc) {S : Set ℝ}
    (hS : S ⊆ Set.Icc t₀ t₁) (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {c ν ρ εc : ℝ} (hc : c ≠ 0) (hρ : ρ ≠ 0) (hscale : εc ^ 2 * Q.η = c * ν * ρ⁻¹ * ρ⁻¹)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ht : c⁻¹ * t ∈ S)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (chart t)) (hψ : Differentiable ℝ (label t))
    (hψχ : ∀ y, label t (chart t y) = y) (hχψ : ∀ x, chart t (label t x) = x)
    (hd : ∀ y, (jacMatrix (chart t) y).det = 1)
    (hG : ∀ y, (fun i j => Q.G (c⁻¹ * t) (ρ⁻¹ • y) i j) =
      (jacMatrix (chart t) y)⁻¹ * ((jacMatrix (chart t) y)⁻¹)ᵀ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a t)) (x : Vec 2) :
    pulseMeanField c ρ εc N 0 Q Cc chart label a t x =
      -ν • ∑ k, fderiv ℝ (fun x' => fderiv ℝ (a t) x' (basisVec k)) x (basisVec k) := by
  rw [pulseMeanField_eq_frame c ρ εc N 0 Q Cc chart label a hc x]
  exact quiet_mean_zero P hDsZ hseq hS hq ht hc hρ hscale hχ hψ hψχ hχψ hd hG ha x

include P in
/-- **The pulse means of the grades `2 ≤ r ≤ H` vanish at a quiet time.** -/
theorem pulseMeanField_quiet_high (hDsZ : D ≤ max (k₀ + 1) (L + 2))
    {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q (K₀ + D + 2) (max (k₀ + 1) (L + 2)) t₀ t₁ N H Cc) {S : Set ℝ}
    (hS : S ⊆ Set.Icc t₀ t₁) (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    (c ρ εc : ℝ) (hc : c ≠ 0) (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i)
    {t : ℝ} (ht : c⁻¹ * t ∈ S) {r : ℕ} (hr : 2 ≤ r) (hrH : r ≤ H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (chart t)) (ha : ContDiff ℝ (⊤ : ℕ∞) (a t)) (x : Vec 2) :
    pulseMeanField c ρ εc N r Q Cc chart label a t x = 0 := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun X : Vec 2 => a t (chart t (ρ • X))) :=
    ha.comp (hχ.comp (contDiff_const_smul ρ))
  rw [pulseMeanField_eq_frame c ρ εc N r Q Cc chart label a hc x]
  exact quiet_mean_high P hDsZ hseq hS hq ht hr hrH hA c εc (ρ⁻¹ • label t x)

include P in
/-- **The grade-one pulse mean at a quiet time is minus the physical divergence of the
family edge flux** (hypotheses of `quiet_mean_one` for the chart `chart t` with labels
`label t`). -/
theorem pulseMeanField_quiet_one (F : ChartedFamily ι h D Pc Ctx) (ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (p₀ : Pc) {c lam : ℝ}
    (hQe : Q.edge = liftEdges c lam (F.fiber p₀ (actual p₀))) (hc : c ≠ 0) (he : e ≠ 0)
    (hν : ν ≠ 0) {εc ρ : ℝ} (hρ : ρ ≠ 0) (hscale : Real.sqrt Q.η * εc = e * ρ⁻¹)
    (hlam : lam * ρ⁻¹ = E⁻¹) (hsc : c⁻¹ * (e * (e / ν)) = 1)
    (hDsZ : D ≤ max (k₀ + 1) (L + 2)) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q (K₀ + D + 2) (max (k₀ + 1) (L + 2)) t₀ t₁ N H Cc) (hH : 1 ≤ H)
    {S : Set ℝ} (hS : S ⊆ Set.Icc t₀ t₁)
    (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ht : c⁻¹ * t ∈ S)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (chart t)) (hψ : ContDiff ℝ (⊤ : ℕ∞) (label t))
    (hψχ : ∀ y, label t (chart t y) = y) (hχψ : ∀ x, chart t (label t x) = x)
    (hd : ∀ y, (jacMatrix (chart t) y).det = 1) (ha : ContDiff ℝ (⊤ : ℕ∞) (a t)) (v : ι)
    (hflux : ∀ x' (a₀ : Fin 2), ∑ i' : ι, ∑ d : admissibleOrders K D v i',
        edgeCoefficient F ν e E actual K v i' d t x'
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => a t y i') x') a₀ =
      ∑ i₀ : Fin 2, chartInvJacobian (label t) x' a₀ i₀ •
        labelEdgeFlux F ν e E p₀ (actual p₀) t (fun y => a t (chart t y)) v (label t x') i₀)
    (x : Vec 2) :
    pulseMeanField c ρ εc N 1 Q Cc chart label a t x v =
      -∑ a₀ : Fin 2, fderiv ℝ (fun x' => ∑ i' : ι, ∑ d : admissibleOrders K D v i',
        edgeCoefficient F ν e E actual K v i' d t x'
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => a t y i') x') a₀) x (basisVec a₀) := by
  rw [pulseMeanField_eq_frame c ρ εc N 1 Q Cc chart label a hc x]
  exact quiet_mean_one P F ν e E actual K p₀ hQe hc he hν hρ hscale hlam hsc hDsZ hseq hH hS hq
    ht hχ hψ hψχ hχψ hd ha v hflux x

end Setting

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Changing the drift scales of a coarse setting**. The premises `IsCoarseSetting` of the
coarse proposition hold with any other drift scales `(a', B₀', lam')` satisfying the drift clauses,
and with the nonnegative constants `|C_*|`, `max Θ 0` (`IsCoarseSetting.rescale`): the remaining
clauses do not mention the drift scales, the edge matrix is entrywise nonnegative, and
`C_*^r ≤ |C_*|^r`. This is how the coarse bound is applied with the actual drift scales of the
background stream (`coarse_drift_small`), which make `q₀ ≲ E^{2δ}`. -/

/-- **A coarse setting with other drift scales and nonnegative constants.** -/
theorem IsCoarseSetting.rescale {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}
    (hcs : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {a' B₀' lam' : ℝ} (ha' : 0 ≤ a') (hB₀' : 1 ≤ B₀') (hlam' : 0 < lam')
    (hjets' : ∀ l : ℕ, 1 ≤ l → l ≤ N → ∀ t ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (b t)) l x‖ ≤
        a' * B₀' ^ l * (l.factorial : ℝ) * lam' ^ ((1 : ℤ) - l))
    (hscale' : B₀' * ρ / lam' ≤ 1 / 2) (hsmall' : a' * B₀' * ρ ^ 2 ≤ B / 8) :
    IsCoarseSetting t₀ t₁ ρ B a' B₀' lam' b D H p J k L N Jm AD CE π Aedge |Cstar|
      (max Θ 0) where
  window := hcs.window
  rho_pos := hcs.rho_pos
  B_pos := hcs.B_pos
  D_ge := hcs.D_ge
  p_pos := hcs.p_pos
  L_eq := hcs.L_eq
  N_eq := hcs.N_eq
  mass_pos := hcs.mass_pos
  drift_bdd := hcs.drift_bdd
  drift_meas := hcs.drift_meas
  drift_smooth := hcs.drift_smooth
  drift_div := hcs.drift_div
  drift_per := hcs.drift_per
  a_nonneg := ha'
  B₀_ge := hB₀'
  lam_pos := hlam'
  drift_jets := hjets'
  drift_scale := hscale'
  drift_small := hsmall'
  J_symm := hcs.J_symm
  J_meas := hcs.J_meas
  J_bdd := hcs.J_bdd
  cov_small := hcs.cov_small
  AD_meas := hcs.AD_meas
  AD_smooth := hcs.AD_smooth
  AD_per := hcs.AD_per
  AD_fin := hcs.AD_fin
  CE_meas := hcs.CE_meas
  CE_smooth := hcs.CE_smooth
  CE_per := hcs.CE_per
  CE_fin := hcs.CE_fin
  edge_nonneg := hcs.edge_nonneg
  edge_row v := (hcs.edge_row v).trans (le_max_left _ _)
  edge_col u := (hcs.edge_col u).trans (le_max_left _ _)
  edge_acyclic := hcs.edge_acyclic
  edge_mean r hr v u := (hcs.edge_mean r hr v u).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (abs_pow Cstar r).le)
      (Assembly.matrix_pow_apply_nonneg hcs.edge_nonneg r v u)))

end AVRegularity.CycleComparison.Reconstruction
end
