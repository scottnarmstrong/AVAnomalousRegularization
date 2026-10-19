-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.TimeIntegration
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.CycleComparison.Residual.TailJets.Main

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The positive slow jets of the dilated coarse field `a_ρ(X) = a(ρX)` on the slow cell, in terms
of the physical factorial norms (each slow derivative of `a_ρ` costs `ρ`, and the slow cell has
volume `ρ⁻²`). -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A positive slow jet of the dilated field on the slow cell is controlled by the gradient
factorial norm. -/
theorem lintegral_slowCell_iteratedFDeriv_dilate_le (m q : ℕ) (hq1 : 1 ≤ q) (hqm : q ≤ m + 1)
    {g : Vec 2 → F} (hg : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) g) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ X in slowCell ρ, ‖iteratedFDeriv ℝ q (fun X' => g (ρ • X')) X‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 ^ q * ((q - 1).factorial : ℝ) ^ 2) * classicalGradFactorialSq ρ m g := by
  have hgq : ContDiff ℝ (q : ℕ∞) g := hg.of_le (by exact_mod_cast hqm)
  have hpt : ∀ X : Vec 2, ‖iteratedFDeriv ℝ q (fun X' => g (ρ • X')) X‖ₑ ^ 2 =
      ENNReal.ofReal (ρ ^ (2 * q)) * ‖iteratedFDeriv ℝ q g (ρ • X)‖ₑ ^ 2 := by
    intro X
    rw [enorm_sq_eq_ofReal', enorm_sq_eq_ofReal', iteratedFDeriv_comp_smul_norm q g hgq ρ X,
      ← ENNReal.ofReal_mul (by positivity), abs_of_pos hρ]
    congr 1
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_slowCell_comp_smul' (fun x => iteratedFDeriv ℝ q g x) hρ]
  have hJ := lintegral_iteratedFDeriv_sq_le_classicalGradFactorialSq m q hq1 hqm hg hρ
  calc ENNReal.ofReal (ρ ^ (2 * q)) * (ENNReal.ofReal (ρ⁻¹ ^ 2) *
        ∫⁻ x in AVenhance.unitCube, ‖iteratedFDeriv ℝ q g x‖ₑ ^ 2)
      = ENNReal.ofReal (ρ⁻¹ ^ 2) * (ENNReal.ofReal (ρ ^ (2 * q)) *
          ∫⁻ x in AVenhance.unitCube, ‖iteratedFDeriv ℝ q g x‖ₑ ^ 2) := by ring
    _ ≤ ENNReal.ofReal (ρ⁻¹ ^ 2) * (ENNReal.ofReal (2 ^ q * ((q - 1).factorial : ℝ) ^ 2 * ρ ^ 2) *
          classicalGradFactorialSq ρ m g) := by gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

end AVRegularity
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity

/-! The finite antidivergence (cleanup) identity of a cell residual:
`[f₀ + div_z F₀]_diag = div_x(e ∑_{j<A} ϑ^j (V_j)_diag) + ϑ^A (f_A)_diag`, `ϑ = e/ρ`.
It is the two-scale chain rule `e div_x V_diag = (div_z V)_diag + ϑ (div_X V)_diag` summed along
the cleanup chain, which telescopes. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The physical divergence of a sampled box-smooth vector field. -/
theorem IsBoxSmooth.sum_fderiv_diag {sX sZ : ℕ} {P : Vec 2 → Vec 2 → Fin 2 → E}
    (hP : IsBoxSmooth sX sZ P) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) (ρ e : ℝ) (x : Vec 2) :
    ∑ k : Fin 2, fderiv ℝ (fun x' => P (ρ⁻¹ • x') (e⁻¹ • x') k) x (basisVec k) =
      ρ⁻¹ • ∑ k : Fin 2, AVRegularity.slowPartial k (fun X z => P X z k) (ρ⁻¹ • x) (e⁻¹ • x)
        + e⁻¹ • ∑ k : Fin 2, AVRegularity.fastPartial k (fun X z => P X z k) (ρ⁻¹ • x) (e⁻¹ • x) := by
  simp only [hP.fderiv_diag_component hX hZ, Finset.sum_add_distrib, Finset.smul_sum]
  rfl

/-- The sampled component of a box-smooth vector field is differentiable. -/
theorem IsBoxSmooth.differentiableAt_diag_component {sX sZ : ℕ}
    {P : Vec 2 → Vec 2 → Fin 2 → E} (hP : IsBoxSmooth sX sZ P) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ)
    (ρ e : ℝ) (x : Vec 2) (k : Fin 2) :
    DifferentiableAt ℝ (fun x' => P (ρ⁻¹ • x') (e⁻¹ • x') k) x := by
  have hg : DifferentiableAt ℝ (fun x' : Vec 2 => (ρ⁻¹ • x', e⁻¹ • x')) x := by fun_prop
  have hd : DifferentiableAt ℝ (fun x' => P (ρ⁻¹ • x') (e⁻¹ • x')) x :=
    (hP.hasFDerivAt_uncurry hX hZ _).differentiableAt.comp x hg
  exact (differentiableAt_apply k _).comp x hd

/-- The zero field is box smooth. -/
theorem isBoxSmooth_zero (sX sZ : ℕ) : IsBoxSmooth sX sZ (fun (_ _ : Vec 2) => (0 : E)) := by
  refine ⟨fun _ => contDiff_const, fun b _ z => ?_, fun a b _ _ => ?_⟩
  · simp only [iteratedFDeriv_fun_zero, Pi.zero_apply]
    exact contDiff_const
  · simp only [iteratedFDeriv_fun_zero, Pi.zero_apply]
    exact continuous_const

/-- Every member of a cleanup chain of a box-smooth flux is box smooth. -/
theorem IsCleanupChain.isBoxSmooth {sX sZ A : ℕ} {f₀ : Vec 2 → Vec 2 → E}
    {F₀ : Vec 2 → Vec 2 → Fin 2 → E} {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hF : IsBoxSmooth sX sZ F₀) (hV : IsCleanupChain sX sZ A f₀ F₀ V) :
    ∀ j, j < A → IsBoxSmooth sX sZ (V j) := by
  obtain ⟨⟨W₀, hW₀, hV0⟩, hVj⟩ := hV
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [hV0]; exact hF.add hW₀.1
  · exact (hVj j hjpos hj).1

/-- The sampled cleanup flux of a chain of box-smooth fields is differentiable. -/
theorem differentiableAt_cleanupFlux {sX sZ A : ℕ} (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) (c ρ e : ℝ)
    {Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E} (t : ℝ)
    (hV : ∀ j, j < A → IsBoxSmooth sX sZ (Vc j (c * t))) (x : Vec 2) (k : Fin 2) :
    DifferentiableAt ℝ (fun x' => cleanupFlux c ρ e A Vc t x' k) x := by
  unfold cleanupFlux diagSample
  refine DifferentiableAt.const_smul (DifferentiableAt.fun_sum fun j hj => ?_) e
  exact ((hV j (Finset.mem_range.1 hj)).differentiableAt_diag_component hX hZ ρ e x k).const_smul _

/-- The cleanup identity at a fixed cell time. -/
theorem cleanup_identity {sX sZ A : ℕ} (hA : 1 ≤ A) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ)
    {ρ e : ℝ} (hρ : ρ ≠ 0) (he : e ≠ 0)
    {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E} {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hF : IsBoxSmooth sX sZ F₀) (hV : IsCleanupChain sX sZ A f₀ F₀ V) (x : Vec 2) :
    f₀ (ρ⁻¹ • x) (e⁻¹ • x) + ∑ k : Fin 2, AVRegularity.fastPartial k (fun X z => F₀ X z k) (ρ⁻¹ • x) (e⁻¹ • x)
      = ∑ k : Fin 2, fderiv ℝ (fun x' => e • ∑ j ∈ Finset.range A,
            (e / ρ) ^ j • V j (ρ⁻¹ • x') (e⁻¹ • x') k) x (basisVec k)
        + (e / ρ) ^ A • cleanupSource V A (ρ⁻¹ • x) (e⁻¹ • x) := by
  obtain ⟨⟨W₀, hW₀, hV0⟩, hVj⟩ := hV
  set X₀ := ρ⁻¹ • x
  set z₀ := e⁻¹ • x
  -- box smoothness of every member of the chain
  have hbox : ∀ j, j < A → IsBoxSmooth sX sZ (V j) :=
    IsCleanupChain.isBoxSmooth hF ⟨⟨W₀, hW₀, hV0⟩, hVj⟩
  -- fast divergences along the chain
  set dX : ℕ → E := fun j => ∑ k : Fin 2, AVRegularity.slowPartial k (fun X z => V j X z k) X₀ z₀
  set dZ : ℕ → E := fun j => ∑ k : Fin 2, AVRegularity.fastPartial k (fun X z => V j X z k) X₀ z₀
  have hdZ0 : dZ 0 = f₀ X₀ z₀ + ∑ k : Fin 2, AVRegularity.fastPartial k (fun X z => F₀ X z k) X₀ z₀ := by
    obtain ⟨-, -, φ, -, -, -, -, hdiv⟩ := id hW₀
    have hsZ : ((sZ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : sZ ≠ 0)
    simp only [dZ, hV0, AVRegularity.fastPartial]
    rw [← hdiv X₀ z₀, add_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : DifferentiableAt ℝ (fun z' => F₀ X₀ z' k) z₀ :=
      differentiableAt_pi.1 ((hF.1 X₀).differentiable hsZ z₀) k
    have h2 : DifferentiableAt ℝ (fun z' => W₀ X₀ z' k) z₀ :=
      differentiableAt_pi.1 ((hW₀.1.1 X₀).differentiable hsZ z₀) k
    rw [fderiv_fun_add h1 h2]
    rfl
  have hdZ : ∀ j, 1 ≤ j → j < A → dZ j = -dX (j - 1) := by
    intro j hj1 hjA
    obtain ⟨-, -, φ, -, -, -, -, hdiv⟩ := hVj j hj1 hjA
    simp only [dZ, dX, AVRegularity.fastPartial]
    rw [hdiv X₀ z₀]
    rfl
  have hfA : cleanupSource V A X₀ z₀ = -dX (A - 1) := rfl
  -- the derivative of the sampled flux
  have hflux : ∀ k : Fin 2, fderiv ℝ (fun x' => e • ∑ j ∈ Finset.range A,
      (e / ρ) ^ j • V j (ρ⁻¹ • x') (e⁻¹ • x') k) x (basisVec k) =
      e • ∑ j ∈ Finset.range A, (e / ρ) ^ j •
        fderiv ℝ (fun x' => V j (ρ⁻¹ • x') (e⁻¹ • x') k) x (basisVec k) := by
    intro k
    have hd : ∀ j ∈ Finset.range A,
        DifferentiableAt ℝ (fun x' => (e / ρ) ^ j • V j (ρ⁻¹ • x') (e⁻¹ • x') k) x := by
      intro j hj
      exact ((hbox j (Finset.mem_range.1 hj)).differentiableAt_diag_component hX hZ ρ e x k).const_smul _
    rw [fderiv_fun_const_smul (DifferentiableAt.fun_sum hd), fderiv_fun_sum hd]
    simp only [FunLike.coe_smul, FunLike.coe_sum, Pi.smul_apply, Finset.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [fderiv_fun_const_smul
      ((hbox j (Finset.mem_range.1 hj)).differentiableAt_diag_component hX hZ ρ e x k)]
    rfl
  simp only [hflux]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.smul_sum]
  have hstep : ∀ j ∈ Finset.range A, (e / ρ) ^ j • ∑ k : Fin 2,
      fderiv ℝ (fun x' => V j (ρ⁻¹ • x') (e⁻¹ • x') k) x (basisVec k) =
      (e / ρ) ^ j • (ρ⁻¹ • dX j + e⁻¹ • dZ j) := by
    intro j hj
    rw [(hbox j (Finset.mem_range.1 hj)).sum_fderiv_diag hX hZ ρ e x]
  rw [Finset.sum_congr rfl hstep, hfA, ← hdZ0]
  -- telescoping
  obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set ϑ := e / ρ with hϑ
  have hterm : ∀ j ∈ Finset.range (B + 1), e • ((e / ρ) ^ j • (ρ⁻¹ • dX j + e⁻¹ • dZ j)) =
      ϑ ^ (j + 1) • dX j + ϑ ^ j • dZ j := by
    intro j _
    simp only [smul_add, smul_smul]
    congr 2
    · rw [hϑ, pow_succ]; field_simp
    · rw [hϑ]; field_simp
  rw [Finset.smul_sum, Finset.sum_congr rfl hterm, Finset.sum_range_succ']
  have hshift : ∀ j ∈ Finset.range B, ϑ ^ (j + 1 + 1) • dX (j + 1) + ϑ ^ (j + 1) • dZ (j + 1) =
      ϑ ^ (j + 1 + 1) • dX (j + 1) - ϑ ^ (j + 1) • dX j := by
    intro j hj
    rw [hdZ (j + 1) (by omega) (by have := Finset.mem_range.1 hj; omega)]
    simp [sub_eq_add_neg]
  rw [Finset.sum_congr rfl hshift,
    Finset.sum_range_sub (fun j => ϑ ^ (j + 1) • dX j) B]
  simp only [zero_add, pow_one, pow_zero, one_smul, smul_neg]
  abel

end AVRegularity
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Slow smoothness of products with continuous linear maps, and of lift actions. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A field whose slow partials are slow smooth of order `m` is slow smooth of order `m + 1`. -/
theorem IsSlowSmooth.of_slowPartial {m : ℕ} {g : Vec 2 → Vec 2 → F}
    (hg1 : ∀ y, ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (fun X => g X y))
    (hc : Continuous (fun p : Vec 2 × Vec 2 => g p.1 p.2))
    (hk : ∀ k : Fin 2, IsSlowSmooth m (AVRegularity.slowPartial k g)) : IsSlowSmooth (m + 1) g := by
  refine ⟨hg1, fun a ha => ?_⟩
  cases a with
  | zero =>
    have : (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ 0 (fun X => g X p.2) p.1) =
        fun p => (continuousMultilinearCurryFin0 ℝ (Vec 2) F).symm (g p.1 p.2) := rfl
    rw [this]
    exact (LinearIsometryEquiv.continuous _).comp hc
  | succ b =>
    have hb : b ≤ m := by omega
    let L : Fin 2 → F →L[ℝ] (Vec 2 →L[ℝ] F) := fun k =>
      (ContinuousLinearMap.smulRightL ℝ (Vec 2) F) (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 2 => ℝ) k)
    have hfd : ∀ (f : Vec 2 → F) (X : Vec 2), fderiv ℝ f X =
        ∑ k, L k (fderiv ℝ f X (basisVec k)) := by
      intro f X
      ext v
      have hv : v = ∑ k, v k • basisVec k := vec2_eq_sum_basisVec v
      conv_lhs => rw [hv]
      simp [L, map_smul]
    have h : (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ (b + 1) (fun X => g X p.2) p.1) =
        fun p => (continuousMultilinearCurryRightEquiv' ℝ b (Vec 2) F).symm
          (∑ k, ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin b => Vec 2) F
            (Vec 2 →L[ℝ] F) (L k)
            (iteratedFDeriv ℝ b (fun X => AVRegularity.slowPartial k g X p.2) p.1)) := by
      funext p
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp only [Function.comp_apply]
      congr 1
      have e : (fun y => fderiv ℝ (fun X => g X p.2) y) =
          fun y => ∑ k, L k (AVRegularity.slowPartial k g y p.2) := funext fun y => hfd _ y
      rw [e]
      have hsum := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ)
        (f := fun (k : Fin 2) (z : Vec 2) => L k (AVRegularity.slowPartial k g z p.2))
        (u := Finset.univ) (n := b) (x := p.1) fun k _ =>
        ((L k).contDiff.comp ((hk k).1 p.2 |>.of_le (by exact_mod_cast hb))).contDiffAt
      rw [hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact (L k).iteratedFDeriv_comp_left (((hk k).1 p.2).contDiffAt) (by exact_mod_cast hb)
    rw [h]
    refine (LinearIsometryEquiv.continuous _).comp (continuous_finsetSum _ fun k _ => ?_)
    exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin b => Vec 2) F
      (Vec 2 →L[ℝ] F) (L k)).continuous.comp ((hk k).2 b hb)

section ClmApply

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

theorem isSlowSmooth_clm_apply_aux : ∀ (m : ℕ) {c : Vec 2 → Vec 2 → (E →L[ℝ] G)},
    IsSlowSmooth m c → ∀ {w : Vec 2 → E}, ContDiff ℝ (m : ℕ∞) w →
      IsSlowSmooth m (fun X y => c X y (w X)) := by
  intro m
  induction m with
  | zero =>
    intro c hc w hw
    refine ⟨fun y => (hc.1 y).clm_apply hw, fun a ha => ?_⟩
    obtain rfl : a = 0 := by omega
    have : (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ 0 (fun X => c X p.2 (w X)) p.1) =
        fun p => (continuousMultilinearCurryFin0 ℝ (Vec 2) G).symm (c p.1 p.2 (w p.1)) := rfl
    rw [this]
    exact (LinearIsometryEquiv.continuous _).comp
      (hc.continuous_uncurry.clm_apply (hw.continuous.comp continuous_fst))
  | succ m ih =>
    intro c hc w hw
    have hw1 : (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    refine IsSlowSmooth.of_slowPartial (fun y => (hc.1 y).clm_apply hw)
      (hc.continuous_uncurry.clm_apply (hw.continuous.comp continuous_fst)) fun k => ?_
    have heq : AVRegularity.slowPartial k (fun X y => c X y (w X)) =
        fun X y => AVRegularity.slowPartial k c X y (w X) +
          c X y (fderiv ℝ w X (basisVec k)) := by
      funext X y
      simp only [AVRegularity.slowPartial]
      rw [fderiv_clm_apply ((hc.1 y).differentiable hw1 X) (hw.differentiable hw1 X)]
      simp [add_comm]
    rw [heq]
    refine (ih (hc.slowPartial k) (hw.of_le (by exact_mod_cast Nat.le_succ m))).add
      (ih (hc.mono (Nat.le_succ m)) ?_)
    exact (hw.fderiv_right (by exact_mod_cast le_rfl)).clm_apply contDiff_const

theorem IsSlowSmooth.clm_apply {m : ℕ} {c : Vec 2 → Vec 2 → (E →L[ℝ] G)}
    (hc : IsSlowSmooth m c) {w : Vec 2 → E} (hw : ContDiff ℝ (m : ℕ∞) w) :
    IsSlowSmooth m (fun X y => c X y (w X)) :=
  isSlowSmooth_clm_apply_aux m hc hw

end ClmApply

section Pi

variable {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, NormedSpace ℝ (H i)]

/-- A `Pi`-valued field is slow smooth when all its components are. -/
theorem IsSlowSmooth.pi {m : ℕ} {φ : Vec 2 → Vec 2 → ∀ i, H i}
    (hφ : ∀ v, IsSlowSmooth m (fun X y => φ X y v)) : IsSlowSmooth m φ := by
  classical
  have h : φ = fun X y => ∑ v, (ContinuousLinearMap.single ℝ H v) (φ X y v) := by
    funext X y
    ext w
    simp [Finset.sum_apply]
  rw [h]
  exact IsSlowSmooth.sum _ fun v _ => (hφ v).clm_comp (ContinuousLinearMap.single ℝ H v)

theorem isSlowSmooth_liftApply (M m : ℕ) (c : LiftCoeff ι H) (a : ℝ → Vec 2 → ∀ i, H i)
    (t : ℝ) (hc : ∀ m' α v u, IsSlowSmooth m (fun X y => c m' α t X y v u))
    (ha : ContDiff ℝ ((m + M : ℕ) : ℕ∞) (a t)) :
    IsSlowSmooth m (fun X y => liftApply M c a t X y) := by
  refine IsSlowSmooth.pi fun v => ?_
  show IsSlowSmooth m (fun X y => ∑ m' ∈ Finset.range (M + 1), ∑ α : DerivativeWord2 m',
    ∑ u : ι, c m' α t X y v u (orderedDerivative α (a t) X u))
  refine IsSlowSmooth.sum _ fun m' hm' => IsSlowSmooth.sum _ fun α _ =>
    IsSlowSmooth.sum _ fun u _ => ?_
  exact (hc m' α v u).clm_apply (contDiff_orderedDerivative_comp
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm')) α ha u)

end Pi

end AVRegularity
end
end

section
/-! Facade: the fibrewise `L²` bound for the cell antidivergence with slow derivatives
(`cellAntidivergence_orderedDerivative_sq_le`), and the `IsSlowSmooth` algebra it uses. -/
end

section
/-! Facade for the jet estimates of the cycle residual: multilinear expansion and word
derivatives, the lift Leibniz bound, the weighted Schur test, slow dilation and energy conversion,
and continuous linear images of box smooth fields and cell antidivergences. -/
end

section
section
/-! Two-scale sampling inequality (facade): `diag_sampling_sq_le`, `lintegral_slowCell_comp_smul'`,
`orderedDerivative_comp_smul`. The proof is elementary (sampling on squares by the fundamental
theorem of calculus in each variable and Cauchy–Schwarz, then a tiling of the unit torus by cells
of side `e`) and lives in the modules under `Residual/Sampling/`. -/
end

section
/-! Facade: the Schur-weighted fibrewise slow jet bounds for lift actions (`schurSums_mono`,
`sum_mass_lintegral_iteratedFDeriv_liftApply_le` and its flux version). -/
end
end
