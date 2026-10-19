-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Velocity.Port.MaterialGoalSource
import AVenhance.Infra.Flow.JointSmoothFromFixedStart
import AVRegularity.CycleReference.ChartIntegrandAlgebra
public import AVRegularity.Statements.Construction.IsFastProfile
import AVRegularity.CycleReference.TransitionZero
public import AVRegularity.Definitions.Construction.DiagLetter
public import AVRegularity.Statements.Construction.IsOCStreamSeq
import AVRegularity.CycleReference.SingleModeFlux
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.Int.Star

@[expose] public section

section
open Homogenization AVenhance
namespace AVRegularity.StrainPhysical

/-! Transport of a stream function by the stream flow: with `X_t = X(t, ·, s)` and
`Ψ = X(s, ·, t)`, `σ∇(ψ∘Ψ)(x) = D X_t(Ψ x) σ∇ψ(Ψ x)` (determinant one). -/

section
open AVRegularity.Velocity.Port.Section2FlowIdentities (left_inverse_entries_of_det_one
  linearMap_apply_two)

variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)

theorem isFlow_stream : IsFlow (streamVel φ) (AVRegularity.streamFlow φ hφ) :=
  flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz

theorem flow_left (t s : ℝ) (x : Vec 2) :
    AVRegularity.streamFlow φ hφ t (AVRegularity.streamFlow φ hφ s x t) s = x := by
  have hX := isFlow_stream hφ
  exact (Infra.Flow.flow_group_law _ hφ.vel_lipschitz hX x t s t).trans (hX.1 x t)

theorem flow_right (t s : ℝ) (x : Vec 2) :
    AVRegularity.streamFlow φ hφ s (AVRegularity.streamFlow φ hφ t x s) t = x := by
  have hX := isFlow_stream hφ
  exact (Infra.Flow.flow_group_law _ hφ.vel_lipschitz hX x s t s).trans (hX.1 x s)

theorem det_one (t s : ℝ) (y : Vec 2) :
    (fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ t z s) y).det = 1 :=
  Infra.Flow.flow_spatial_jacobian_det_eq_one_of_divergence_free
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ) (isFlow_stream hφ)
    (fun u x => AVRegularity.Velocity.Port.Section2FlowIdentities.streamVel_spatialDivergence_eq_zero
      hφ u x) y s t

theorem differentiable_flow (t s : ℝ) :
    Differentiable ℝ (fun z => AVRegularity.streamFlow φ hφ t z s) :=
  (AVRegularity.CycleReference.streamFlow_spatial_smooth hφ t s).differentiable (by simp)

/-- Cofactor entries of the derivative of `Ψ = X(s, ·, t)` in terms of those of `X_t` at `Ψ x`. -/
theorem inv_entries (t s : ℝ) (x : Vec 2) :
    let A := fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ s z t) x
    let B := fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ t z s)
      (AVRegularity.streamFlow φ hφ s x t)
    A (basisVec 0) 0 = B (basisVec 1) 1 ∧ A (basisVec 1) 0 = -B (basisVec 1) 0 ∧
    A (basisVec 0) 1 = -B (basisVec 0) 1 ∧ A (basisVec 1) 1 = B (basisVec 0) 0 := by
  intro A B
  set y := AVRegularity.streamFlow φ hφ s x t with hy
  have hFy : AVRegularity.streamFlow φ hφ t y s = x := flow_left hφ t s x
  have hB : HasFDerivAt (fun z => AVRegularity.streamFlow φ hφ t z s) B y :=
    ((differentiable_flow hφ t s) y).hasFDerivAt
  have hA : HasFDerivAt (fun z => AVRegularity.streamFlow φ hφ s z t) A
      (AVRegularity.streamFlow φ hφ t y s) := by
    rw [hFy]; exact ((differentiable_flow hφ s t) x).hasFDerivAt
  have hchain := HasFDerivAt.comp y hA hB
  have hid := hchain.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun z => (flow_right hφ t s z).symm)
  have hcomp : A.comp B = ContinuousLinearMap.id ℝ (Vec 2) := hid.unique (hasFDerivAt_id y)
  exact left_inverse_entries_of_det_one hcomp (det_one hφ t s y)

theorem clm_two (L : Vec 2 →L[ℝ] ℝ) (v : Vec 2) :
    L v = L (basisVec 0) * v 0 + L (basisVec 1) * v 1 := by
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    ext j
    fin_cases j <;> simp [basisVec]
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

theorem streamVel_const (F : Vec 2 → ℝ) (x : Vec 2) :
    streamVel (fun _ => F) 0 x = ![-(spaceGrad F x 1), spaceGrad F x 0] := by
  ext i
  fin_cases i <;> simp [streamVel, AVenhance.sigmaMat, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-- `σ∇(ψ∘Ψ)(x) = D X_t(Ψ x) σ∇ψ(Ψ x)`. -/
theorem stream_transport (t s : ℝ) {ψ : Vec 2 → ℝ} (x : Vec 2)
    (hψ : DifferentiableAt ℝ ψ (AVRegularity.streamFlow φ hφ s x t)) :
    streamVel (fun _ => ψ ∘ fun z => AVRegularity.streamFlow φ hφ s z t) 0 x =
      fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ t z s)
        (AVRegularity.streamFlow φ hφ s x t)
        (streamVel (fun _ => ψ) 0 (AVRegularity.streamFlow φ hφ s x t)) := by
  obtain ⟨e1, e2, e3, e4⟩ := inv_entries hφ t s x
  set y := AVRegularity.streamFlow φ hφ s x t with hy
  set B := fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ t z s) y with hB
  set A := fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ s z t) x with hA
  have hPsi : DifferentiableAt ℝ (fun z => AVRegularity.streamFlow φ hφ s z t) x :=
    differentiable_flow hφ s t x
  have hgrad : ∀ k : Fin 2, spaceGrad (ψ ∘ fun z => AVRegularity.streamFlow φ hφ s z t) x k =
      fderiv ℝ ψ y (basisVec 0) * A (basisVec k) 0 +
        fderiv ℝ ψ y (basisVec 1) * A (basisVec k) 1 := by
    intro k
    simp only [spaceGrad]
    rw [fderiv_comp x hψ hPsi]
    change fderiv ℝ ψ y (A (basisVec k)) = _
    rw [clm_two]
  set g0 := fderiv ℝ ψ y (basisVec 0)
  set g1 := fderiv ℝ ψ y (basisVec 1)
  have hg : ∀ k : Fin 2, spaceGrad ψ y k = if k = 0 then g0 else g1 := by
    intro k; fin_cases k <;> simp [spaceGrad, g0, g1]
  have hL := streamVel_const (ψ ∘ fun z => AVRegularity.streamFlow φ hφ s z t) x
  have hR := streamVel_const ψ y
  rw [hL, hR]
  have h0 : spaceGrad ψ y 0 = g0 := by simp [spaceGrad, g0]
  have h1 : spaceGrad ψ y 1 = g1 := by simp [spaceGrad, g1]
  rw [h0, h1]
  have hB0 : B ![-g1, g0] 0 = B (basisVec 0) 0 * (-g1) + B (basisVec 1) 0 * g0 := by
    rw [linearMap_apply_two]; simp
  have hB1 : B ![-g1, g0] 1 = B (basisVec 0) 1 * (-g1) + B (basisVec 1) 1 * g0 := by
    rw [linearMap_apply_two]; simp
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [hgrad 1, hB0, e2, e4]
    ring
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hgrad 0, hB1, e1, e3]
    ring
end

/-! Jacobian of the transported field `y ↦ DX(y) w(y)`: by symmetry of second derivatives,
`D(DX · w)(Y)_{ak} = (∂_w DX)_{ak} + (DX Dw)_{ak}`. -/

section
open AVRegularity.Velocity.Port.Section2FlowIdentities (linearMap_apply_two)

theorem jac_transported {X : Vec 2 → Vec 2} (hX : ContDiff ℝ (⊤ : ℕ∞) X) {w : Vec 2 → Vec 2}
    (hw : Differentiable ℝ w) (Y : Vec 2) (a k : Fin 2) :
    jacMatrix (fun y => fderiv ℝ X y (w y)) Y a k =
      fderiv ℝ (fun y => jacMatrix X y a k) Y (w Y) + (jacMatrix X Y * jacMatrix w Y) a k := by
  have hc : Differentiable ℝ (fderiv ℝ X) :=
    (hX.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ X Y := hX.contDiffAt.isSymmSndFDerivAt (by simp)
  have hV := fderiv_clm_apply (hc Y) (hw Y)
  have h1 : jacMatrix (fun y => fderiv ℝ X y (w y)) Y a k =
      (fderiv ℝ X Y (fderiv ℝ w Y (basisVec k)) +
        fderiv ℝ (fderiv ℝ X) Y (basisVec k) (w Y)) a := by
    simp only [jacMatrix, Matrix.of_apply]
    rw [hV]
    rfl
  have hΛ : HasFDerivAt (fun y => jacMatrix X y a k)
      (((ContinuousLinearMap.proj a).comp
        (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec k))).comp (fderiv ℝ (fderiv ℝ X) Y)) Y := by
    have := ((ContinuousLinearMap.proj a).comp
      (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec k))).hasFDerivAt.comp Y (hc Y).hasFDerivAt
    exact this
  rw [hΛ.fderiv, h1]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.proj_apply, Pi.add_apply]
  have hM : (jacMatrix X Y * jacMatrix w Y) a k =
      fderiv ℝ X Y (fderiv ℝ w Y (basisVec k)) a := by
    rw [linearMap_apply_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [jacMatrix]
  rw [hM, hsymm (basisVec k) (w Y), add_comm]
end

/-! The variational equation for the spatial Jacobian of the stream flow:
`∂_t F = D𝐛(t, X) F`, from the symmetry of second derivatives of the joint flow. -/

section
variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)

theorem joint_smooth (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => AVRegularity.streamFlow φ hφ p.1 p.2 s) := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hs := Infra.Flow.flow_joint_contDiff_infty hb (isFlow_stream hφ)
  exact hs.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))

theorem fderiv_slice_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Vec 2 → E} (hf : Differentiable ℝ f) (t : ℝ) (x v : Vec 2) :
    fderiv ℝ (fun y => f (t, y)) x v = fderiv ℝ f (t, x) (0, v) := by
  have hg : HasFDerivAt (fun y : Vec 2 => (t, y))
      ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have h := ((hf (t, x)).hasFDerivAt.comp x hg).fderiv
  change fderiv ℝ (f ∘ Prod.mk t) x = _ at h
  change (fderiv ℝ (f ∘ Prod.mk t) x) v = _
  rw [h]
  simp

theorem partial_t_Z (s : ℝ) (p : ℝ × Vec 2) :
    fderiv ℝ (fun q : ℝ × Vec 2 => AVRegularity.streamFlow φ hφ q.1 q.2 s) p (1, 0) =
      streamVel φ p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s) := by
  have hZ := joint_smooth hφ s
  have hZd : DifferentiableAt ℝ (fun q : ℝ × Vec 2 => AVRegularity.streamFlow φ hφ q.1 q.2 s) p :=
    (hZ.differentiable (by simp)) p
  have hg : HasDerivAt (fun r : ℝ => (r, p.2)) ((1 : ℝ), (0 : Vec 2)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have h1 := (hZd.hasFDerivAt.comp_hasDerivAt p.1 hg)
  have h2 := (isFlow_stream hφ).2 p.2 s p.1
  exact h1.unique h2

theorem jac_time_deriv (t s : ℝ) (Y : Vec 2) (a b : Fin 2) :
    deriv (fun u => jacMatrix (fun y => AVRegularity.streamFlow φ hφ u y s) Y a b) t =
      (jacMatrix (streamVel φ t) (AVRegularity.streamFlow φ hφ t Y s) *
        jacMatrix (fun y => AVRegularity.streamFlow φ hφ t y s) Y) a b := by
  set Z : ℝ × Vec 2 → Vec 2 := fun q => AVRegularity.streamFlow φ hφ q.1 q.2 s with hZdef
  have hZ : ContDiff ℝ (⊤ : ℕ∞) Z := joint_smooth hφ s
  have hZd : Differentiable ℝ Z := hZ.differentiable (by simp)
  set L : ℝ × Vec 2 → (ℝ × Vec 2) →L[ℝ] Vec 2 := fderiv ℝ Z with hL
  have hLc : ContDiff ℝ (⊤ : ℕ∞) L := hZ.fderiv_right (by simp)
  have hLd : Differentiable ℝ L := hLc.differentiable (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ Z (t, Y) :=
    hZ.contDiffAt.isSymmSndFDerivAt (by simp)
  have hsym : fderiv ℝ L (t, Y) (1, 0) (0, basisVec b) =
      fderiv ℝ L (t, Y) (0, basisVec b) (1, 0) := hsymm (1, 0) (0, basisVec b)
  -- the time derivative of the column
  have hfun : (fun u => jacMatrix (fun y => AVRegularity.streamFlow φ hφ u y s) Y a b) =
      fun u => L (u, Y) (0, basisVec b) a := by
    funext u
    simp only [jacMatrix, Matrix.of_apply]
    exact congrArg (fun z => z a) (fderiv_slice_gen hZd u Y (basisVec b))
  have hpath : HasDerivAt (fun r : ℝ => (r, Y)) ((1 : ℝ), (0 : Vec 2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t Y)
  have hLder : HasDerivAt (fun r : ℝ => L (r, Y)) (fderiv ℝ L (t, Y) (1, 0)) t :=
    ((hLd (t, Y)).hasFDerivAt.comp_hasDerivAt t hpath)
  set Λ : ((ℝ × Vec 2) →L[ℝ] Vec 2) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj a).comp (ContinuousLinearMap.apply ℝ (Vec 2) (0, basisVec b))
    with hΛ
  have hcol : HasDerivAt (fun r : ℝ => L (r, Y) (0, basisVec b) a)
      (fderiv ℝ L (t, Y) (1, 0) (0, basisVec b) a) t :=
    Λ.hasFDerivAt.comp_hasDerivAt t hLder
  rw [hfun, hcol.deriv, hsym]
  -- the velocity identity
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hbd : Differentiable ℝ (Function.uncurry (streamVel φ)) :=
    hb.smooth.differentiable (by simp)
  have hA : HasFDerivAt (fun p : ℝ × Vec 2 => L p (1, 0))
      ((ContinuousLinearMap.apply ℝ (Vec 2) ((1 : ℝ), (0 : Vec 2))).comp (fderiv ℝ L (t, Y)))
      (t, Y) :=
    (ContinuousLinearMap.apply ℝ (Vec 2) ((1 : ℝ), (0 : Vec 2))).hasFDerivAt.comp (t, Y)
      (hLd (t, Y)).hasFDerivAt
  have hB : HasFDerivAt (fun p : ℝ × Vec 2 => streamVel φ p.1 (Z p))
      ((fderiv ℝ (Function.uncurry (streamVel φ)) (t, Z (t, Y))).comp
        ((ContinuousLinearMap.fst ℝ ℝ (Vec 2)).prod (fderiv ℝ Z (t, Y)))) (t, Y) := by
    have hinner : HasFDerivAt (fun p : ℝ × Vec 2 => (p.1, Z p))
        ((ContinuousLinearMap.fst ℝ ℝ (Vec 2)).prod (fderiv ℝ Z (t, Y))) (t, Y) :=
      (hasFDerivAt_fst).prodMk (hZd (t, Y)).hasFDerivAt
    exact (hbd (t, Z (t, Y))).hasFDerivAt.comp (t, Y) hinner
  have hfeq : (fun p : ℝ × Vec 2 => L p (1, 0)) = fun p => streamVel φ p.1 (Z p) :=
    funext fun p => partial_t_Z hφ s p
  rw [hfeq] at hA
  have huniq := hA.unique hB
  have hw := congrArg (fun T : (ℝ × Vec 2) →L[ℝ] Vec 2 => T (0, basisVec b)) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst'] at hw
  have hslice := fderiv_slice_gen hbd t (Z (t, Y)) (L (t, Y) (0, basisVec b))
  have hXcol : fderiv ℝ (fun y => AVRegularity.streamFlow φ hφ t y s) Y (basisVec b) =
      L (t, Y) (0, basisVec b) := fderiv_slice_gen hZd t Y (basisVec b)
  rw [hw]
  change (fderiv ℝ (Function.uncurry (streamVel φ)) (t, Z (t, Y)) (0, L (t, Y) (0, basisVec b))) a = _
  have hslice' : (fderiv ℝ (Function.uncurry (streamVel φ)) (t, Z (t, Y)))
      (0, (L (t, Y)) (0, basisVec b)) = fderiv ℝ (streamVel φ t) (Z (t, Y))
        ((L (t, Y)) (0, basisVec b)) := hslice.symm
  rw [hslice']
  simp only [Matrix.mul_apply, jacMatrix, Matrix.of_apply, hXcol]
  have := AVRegularity.Velocity.Port.Section2FlowIdentities.linearMap_apply_two
    (fderiv ℝ (streamVel φ t) (Z (t, Y))) (L (t, Y) (0, basisVec b)) a
  rw [this, Fin.sum_univ_two]
end

end AVRegularity.StrainPhysical
end

section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.StrainPhysical

/-! On the window of the pulse `pc` the next stream is the previous one plus the transported
pulse term, so `𝐛_i = 𝐛_{i-1} + p_{pc}(t) DX_t(Ψ x) 𝐮_{i,pc}(Ψ x)`. -/

theorem zeta_eq_zero_of_far {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) {u : ℝ} (hu : 2 / 3 ≤ |u|) :
    ζ u = 0 := by
  by_contra h
  have hmem : u ∈ tsupport ζ := subset_tsupport _ (Function.mem_support.2 h)
  have := hζ.2.2.1 hmem
  rw [Set.mem_Ioo] at this
  have := abs_lt.2 this
  linarith

theorem ocShear_eq_zero_of_zero_scale {α q : ℝ} (hα : 0 < α) (hq : 1 < q) {m : ℕ} (hm : 1 ≤ m)
    (k : ℤ) (y : Vec 2) : ocShear α q 0 m k y = 0 := by
  have hexp : q ^ m / (q - 1) ≠ 0 := by
    have : 0 < q ^ m / (q - 1) := div_pos (pow_pos (by linarith) m) (by linarith)
    exact this.ne'
  have hε : ocEpsilon q 0 m = 0 := by
    have hm0 : m ≠ 0 := by omega
    simp [ocEpsilon, hm0, Real.zero_rpow hexp]
  rw [ocShear_sine_formula, hε]
  have : (0 : ℝ) ^ (1 + α) = 0 := Real.zero_rpow (by linarith)
  split_ifs <;> simp [this]

theorem differentiable_slice {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (t : ℝ) :
    Differentiable ℝ (φ t) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (φ t) := by
    have := hφ.1.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec 2 => (t, y)))
    exact this
  exact h.differentiable (by simp)

/-- The increment identity on the window of the pulse `pc` (with `Ψ x = X(s_pc, x, t)`). -/
theorem streamVel_increment {α q : ℝ} (hα : 0 < α) (hq : 1 < q) {Λ : ℕ} {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ} {i : ℕ} (hi : 1 ≤ i)
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
    by_cases hΛ : Λ = 0
    · subst hΛ
      have h0 : ∀ k : ℤ, ∀ y, ocShear α q 0 i k y = 0 := fun k y =>
        ocShear_eq_zero_of_zero_scale hα hq hi k y
      simp [h0]
    · have hΛ1 : 1 ≤ Λ := Nat.one_le_iff_ne_zero.2 hΛ
      have hτ : 0 < ocTau α q Λ i := AVRegularity.Construction.Stream.ocTau_pos hΛ1
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

end AVRegularity.StrainPhysical
end

section
open Homogenization AVenhance
namespace AVRegularity.StrainPhysical

/-! Regularity and the degenerate case of the pulse shear velocity `𝐮_{m,k}`. -/

theorem differentiable_ocShearVel (α q : ℝ) (Λ m : ℕ) (k : ℤ) :
    Differentiable ℝ (ocShearVel α q Λ m k) := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (ocShear α q Λ m k) := AVRegularity.CycleReference.ocShear_contDiff α q Λ m k
  have hc : Differentiable ℝ (fderiv ℝ (ocShear α q Λ m k)) :=
    (hψ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hg : ∀ j : Fin 2, Differentiable ℝ (fun y => spaceGrad (ocShear α q Λ m k) y j) := by
    intro j
    exact (hc.clm_apply (differentiable_const (basisVec j)))
  change Differentiable ℝ (fun y => sigmaMat.mulVec (spaceGrad (ocShear α q Λ m k) y))
  refine differentiable_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact ((differentiable_const _).mul (hg 0)).add ((differentiable_const _).mul (hg 1))

theorem ocShearVel_zero_scale {α q : ℝ} (hα : 0 < α) (hq : 1 < q) {m : ℕ} (hm : 1 ≤ m) (k : ℤ)
    (y : Vec 2) : ocShearVel α q 0 m k y = 0 := by
  have h : ocShear α q 0 m k = fun _ => 0 := funext (ocShear_eq_zero_of_zero_scale hα hq hm k)
  change sigmaMat.mulVec (spaceGrad (ocShear α q 0 m k) y) = 0
  rw [h]
  ext i
  simp [spaceGrad, Matrix.mulVec, dotProduct]

end AVRegularity.StrainPhysical
end

section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.StrainPhysical

/-! Matrix assembly: the Jacobian of `x ↦ 𝐛(t,x) + DX_t(Ψx) w(Ψx)` at `X_t(Y)` and the
strain `(∂_tF)F⁻¹ = D𝐛(t, X_t Y)`. -/

variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)

include hφ

theorem jac_unit (t s : ℝ) (Y : Vec 2) :
    IsUnit (jacMatrix (fun y => AVRegularity.streamFlow φ hφ t y s) Y) := by
  rw [Matrix.isUnit_iff_isUnit_det, streamFlow_jacMatrix_det_one hφ t s Y]
  exact isUnit_one

theorem differentiable_streamVel_slice (t : ℝ) : Differentiable ℝ (streamVel φ t) := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hbd : Differentiable ℝ (Function.uncurry (streamVel φ)) :=
    hb.smooth.differentiable (by simp)
  exact hbd.comp (differentiable_const t |>.prodMk differentiable_id)

theorem famStrain_eq (t s : ℝ) (Y : Vec 2) :
    Matrix.of (fun a b => deriv (fun u =>
      jacMatrix (fun y => AVRegularity.streamFlow φ hφ u y s) Y a b) t) *
      (jacMatrix (fun y => AVRegularity.streamFlow φ hφ t y s) Y)⁻¹ =
    jacMatrix (streamVel φ t) (AVRegularity.streamFlow φ hφ t Y s) := by
  have h : Matrix.of (fun a b => deriv (fun u =>
      jacMatrix (fun y => AVRegularity.streamFlow φ hφ u y s) Y a b) t) =
      jacMatrix (streamVel φ t) (AVRegularity.streamFlow φ hφ t Y s) *
        jacMatrix (fun y => AVRegularity.streamFlow φ hφ t y s) Y := by
    ext a b
    simp only [Matrix.of_apply]
    exact jac_time_deriv hφ t s Y a b
  rw [h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1
    (jac_unit hφ t s Y)), Matrix.mul_one]

theorem jac_increment (t s : ℝ) (Y : Vec 2) {w : Vec 2 → Vec 2} (hw : Differentiable ℝ w) :
    jacMatrix (fun x => streamVel φ t x +
        fderiv ℝ (fun z => AVRegularity.streamFlow φ hφ t z s)
          (AVRegularity.streamFlow φ hφ s x t)
          (w (AVRegularity.streamFlow φ hφ s x t)))
      (AVRegularity.streamFlow φ hφ t Y s) =
    jacMatrix (streamVel φ t) (AVRegularity.streamFlow φ hφ t Y s) +
      (Matrix.of (fun a c => fderiv ℝ (fun y => jacMatrix
          (fun z => AVRegularity.streamFlow φ hφ t z s) y a c) Y (w Y)) +
        jacMatrix (fun z => AVRegularity.streamFlow φ hφ t z s) Y * jacMatrix w Y) *
        (jacMatrix (fun z => AVRegularity.streamFlow φ hφ t z s) Y)⁻¹ := by
  set X : Vec 2 → Vec 2 := fun z => AVRegularity.streamFlow φ hφ t z s with hXdef
  set Ψ : Vec 2 → Vec 2 := fun z => AVRegularity.streamFlow φ hφ s z t with hΨdef
  set x₀ := X Y with hx₀
  have hXs : ContDiff ℝ (⊤ : ℕ∞) X := AVRegularity.CycleReference.streamFlow_spatial_smooth hφ t s
  have hΨ : Differentiable ℝ Ψ := differentiable_flow hφ s t
  have hXd : Differentiable ℝ X := differentiable_flow hφ t s
  have hc : Differentiable ℝ (fderiv ℝ X) :=
    (hXs.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hΨx : Ψ x₀ = Y := flow_right hφ t s Y
  have hXΨ : X (Ψ x₀) = x₀ := flow_left hφ t s x₀
  have hV : Differentiable ℝ (fun y => fderiv ℝ X y (w y)) := hc.clm_apply hw
  have hb := differentiable_streamVel_slice hφ t
  -- jacobian of the inverse
  have hinv : jacMatrix Ψ x₀ = (jacMatrix X Y)⁻¹ := by
    have hcomp := jacMatrix_comp (f := X) (g := Ψ) x₀ (hXd _) (hΨ x₀)
    have hid : X ∘ Ψ = id := funext fun z => flow_left hφ t s z
    rw [hid, jacMatrix_identity, hΨx] at hcomp
    exact (Matrix.inv_eq_right_inv hcomp.symm).symm
  have hsum : jacMatrix (fun x => streamVel φ t x + fderiv ℝ X (Ψ x) (w (Ψ x))) x₀ =
      jacMatrix (streamVel φ t) x₀ + jacMatrix ((fun y => fderiv ℝ X y (w y)) ∘ Ψ) x₀ := by
    ext a k
    simp only [jacMatrix, Matrix.of_apply, Matrix.add_apply]
    have h2 := ((hb x₀).hasFDerivAt.add ((hV.comp hΨ) x₀).hasFDerivAt).fderiv
    have : fderiv ℝ (fun x => streamVel φ t x + ((fun y => fderiv ℝ X y (w y)) ∘ Ψ) x) x₀ =
      fderiv ℝ (streamVel φ t) x₀ + fderiv ℝ ((fun y => fderiv ℝ X y (w y)) ∘ Ψ) x₀ := h2
    change (fderiv ℝ (fun x => streamVel φ t x + ((fun y => fderiv ℝ X y (w y)) ∘ Ψ) x) x₀)
      (basisVec k) a = _
    rw [this]
    simp
  rw [hsum, jacMatrix_comp x₀ (hV _) (hΨ x₀), hΨx, hinv]
  congr 1
  congr 1
  ext a k
  rw [jac_transported hXs hw Y a k]
  simp [Matrix.add_apply]

end AVRegularity.StrainPhysical
end

section
open Homogenization AVenhance AVRegularity
namespace AVRegularity.StrainPhysical

/-! The context strain at a physical context is the velocity gradient `D𝐛_i`. -/

theorem geom_native (D : OCData) (i : ℕ) (hi : 1 ≤ i) (pc : ℤ) (Y : Vec 2) :
    (⟨i - 1, [pc], Y, []⟩ : RealChain).geom D = (D.flowOf (i - 1), Y, D.slotAnchor i pc) := by
  have : i - 1 + 1 = i := by omega
  simp [RealChain.geom, OCData.geomAux, this]

theorem recenter_native (D : OCData) (i : ℕ) (pc : ℤ) (Y h : Vec 2) :
    (⟨i - 1, [pc], Y, []⟩ : RealChain).recenter D h = ⟨i - 1, [pc], Y + h, []⟩ := by
  simp [RealChain.recenter]

theorem label_shear_data (D : OCData) (α q : ℝ) (hα₀ : 0 < α) (hq₁ : 1 < q)
    (hα : D.α = α) (hq : D.q = q) (i : ℕ) (hi : 1 ≤ i) (pc : ℤ) (t : ℝ)
    (Y : Vec 2) :
    labelShear D i pc t ((D.eps i)⁻¹ • Y) =
        ocPulse D.α D.q D.Λ D.ζ i pc t • ocShearVel D.α D.q D.Λ i pc Y ∧
      (D.eps i)⁻¹ • jacMatrix (labelShear D i pc t) ((D.eps i)⁻¹ • Y) =
        jacMatrix (fun y => ocPulse D.α D.q D.Λ D.ζ i pc t • ocShearVel D.α D.q D.Λ i pc y) Y := by
  by_cases hε : D.eps i = 0
  · have hΛ0 : D.Λ = 0 := by
      by_contra hne
      have := AVRegularity.Construction.Stream.ocEpsilon_pos (q := D.q) (n := i)
        (Nat.one_le_iff_ne_zero.2 hne)
      exact this.ne' hε
    have hz : ∀ y, ocShearVel D.α D.q D.Λ i pc y = 0 := by
      intro y
      rw [hΛ0]
      exact ocShearVel_zero_scale (hα ▸ hα₀) (hq ▸ hq₁) hi pc y
    have hL : labelShear D i pc t = fun _ => 0 := by
      funext y; simp [labelShear, hz]
    have hW : (fun y => ocPulse D.α D.q D.Λ D.ζ i pc t • ocShearVel D.α D.q D.Λ i pc y) =
        fun _ => 0 := by
      funext y; simp [hz]
    rw [hL, hW]
    refine ⟨by simp [hz], ?_⟩
    ext a b
    simp [jacMatrix]
  · refine ⟨?_, ?_⟩
    · simp [labelShear, smul_smul, hε]
    · have hcomp : labelShear D i pc t = fun z =>
          (fun y => ocPulse D.α D.q D.Λ D.ζ i pc t • ocShearVel D.α D.q D.Λ i pc y)
            (D.eps i • z) := rfl
      have hdiff : Differentiable ℝ
          (fun y => ocPulse D.α D.q D.Λ D.ζ i pc t • ocShearVel D.α D.q D.Λ i pc y) :=
        (differentiable_ocShearVel D.α D.q D.Λ i pc).const_smul (ocPulse D.α D.q D.Λ D.ζ i pc t)
      have hg : ∀ z : Vec 2, HasFDerivAt (fun z : Vec 2 => D.eps i • z)
          (D.eps i • ContinuousLinearMap.id ℝ (Vec 2)) z :=
        fun z => (hasFDerivAt_id z).const_smul (D.eps i)
      have hJ := AVRegularity.CycleReference.jacMatrix_comp (f := fun y => ocPulse D.α D.q D.Λ D.ζ i pc t •
          ocShearVel D.α D.q D.Λ i pc y) (g := fun z : Vec 2 => D.eps i • z)
        ((D.eps i)⁻¹ • Y) (by simpa [smul_smul, hε] using hdiff.differentiableAt)
        ((hg _).differentiableAt)
      have hg1 : jacMatrix (fun z : Vec 2 => D.eps i • z) ((D.eps i)⁻¹ • Y) =
          D.eps i • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
        ext a b
        simp [jacMatrix, (hg _).fderiv, basisVec, Matrix.one_apply, Pi.single_apply]
      have hgY : D.eps i • (D.eps i)⁻¹ • Y = Y := by simp [smul_smul, hε]
      have hcomp' : jacMatrix (labelShear D i pc t) ((D.eps i)⁻¹ • Y) =
          jacMatrix (fun y => ocPulse D.α D.q D.Λ D.ζ i pc t • ocShearVel D.α D.q D.Λ i pc y) Y *
            (D.eps i • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
        rw [hgY, hg1] at hJ
        exact hJ
      rw [hcomp', Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hε, one_smul]

theorem context_strain_physical_aux (α q : ℝ) (hα₀ : 0 < α) (hq₁ : 1 < q) (Λ : ℕ) (ζ : ℝ → ℝ)
    (hζf : IsFastProfile ζ) (D : OCData) (hα : D.α = α)
    (hq : D.q = q) (hΛ : D.Λ = Λ) (hζ : D.ζ = ζ) (hS : IsOCStreamSeq α q Λ ζ D.Φ)
    (i : ℕ) (hi : 1 ≤ i) (pc : ℤ) (hpc : Odd pc) (t : ℝ) (ht : t ∈ ocPulseWindow α q Λ i pc)
    (Y : Vec 2) :
    contextStrain D i pc t ((nativeChain i pc).recenter D Y) ((D.eps i)⁻¹ • Y) =
      jacMatrix (streamVel (D.Φ i) t)
        ((((nativeChain i pc).recenter D Y).geom D).1 t Y
          (((nativeChain i pc).recenter D Y).geom D).2.2) := by
  obtain ⟨h, hnext⟩ := hS.2 i hi
  have hφ := D.hΦ (i - 1)
  have hnext' : D.Φ i = ocNextStream α q Λ ζ i (D.Φ (i - 1)) hφ := hnext
  have hs : D.slotAnchor i pc = (ocLabel D.α D.q D.Λ i pc : ℝ) * ocTauPP D.α D.q D.Λ i := rfl
  have hinc := streamVel_increment hα₀ hq₁ hζf hi hnext' hpc ht
  rw [← hα, ← hq, ← hΛ, ← hζ] at hinc
  set w : Vec 2 → Vec 2 := fun y =>
    ocPulse D.α D.q D.Λ D.ζ i pc t • ocShearVel D.α D.q D.Λ i pc y with hw
  have hwd : Differentiable ℝ w :=
    (differentiable_ocShearVel D.α D.q D.Λ i pc).const_smul (ocPulse D.α D.q D.Λ D.ζ i pc t)
  have hb : streamVel (D.Φ i) t = fun x => streamVel (D.Φ (i - 1)) t x +
      fderiv ℝ (fun z => AVRegularity.streamFlow (D.Φ (i - 1)) hφ t z (D.slotAnchor i pc))
        (AVRegularity.streamFlow (D.Φ (i - 1)) hφ (D.slotAnchor i pc) x t)
        (w (AVRegularity.streamFlow (D.Φ (i - 1)) hφ (D.slotAnchor i pc) x t)) := by
    funext x
    rw [hinc x, hs]
    simp [hw]
  obtain ⟨hU, hJ⟩ := label_shear_data D α q hα₀ hq₁ hα hq i hi pc t Y
  rw [nativeChain_recenter]
  simp only [contextStrain, RealChain.famStrain, RealChain.famJac, geom_native D i hi pc,
    recenter_native, OCData.flowOf]
  rw [hU, hJ, famStrain_eq hφ t (D.slotAnchor i pc) Y, hb,
    jac_increment hφ t (D.slotAnchor i pc) Y hwd]
  have hG : ∀ (f : Vec 2 → ℝ), fderiv ℝ (fun h => f (Y + h)) 0 = fderiv ℝ f Y := by
    intro f
    rw [fderiv_comp_add_left]
    simp
  have hG' : ∀ (X' : Vec 2 → Vec 2) (a c : Fin 2), fderiv ℝ (fun h => jacMatrix X' (Y + h) a c) 0 =
      fderiv ℝ (fun y => jacMatrix X' y a c) Y := fun X' a c => hG (fun y => jacMatrix X' y a c)
  simp only [hG']
  rfl

end AVRegularity.StrainPhysical
end
