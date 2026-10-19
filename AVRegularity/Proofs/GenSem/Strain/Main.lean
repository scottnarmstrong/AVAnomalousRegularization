-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.JointSourceCongruence
import AVRegularity.CycleReference.TransitionZero
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.CoreFlux

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity AVRegularity.EntryWeakProofs
namespace AVRegularity.Providers.GenSem

/-! Joint `C¹` regularity of the spatial Jacobian of the offset flows of a real chain: for every
anchor `r`, `(u, x) ↦ D_x 𝔛(u, x, r)` is `C¹`. Induction over `geomAux`, as for the flow itself
(`geomC1_geomAux`): the base is a stream flow (jointly smooth); a child composes the parent
flow with `Z = A + κ(u) W` with `A` spatially smooth, `W` smooth and `κ` a `C¹` pulse integral. -/

/-- The spatial Jacobian of the offset flow is jointly `C¹` at every anchor. -/
def GeomJacC1 (g : ChainGeom) : Prop :=
  ∀ r : ℝ, ContDiff ℝ 1 (fun p : ℝ × Vec 2 => fderiv ℝ (fun y => g.1 p.1 y r) p.2)

theorem contDiff_pulseIntegral (D : OCData) (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (r : ℝ) :
    ContDiff ℝ 1 (fun u : ℝ => ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v) := by
  have hc : Continuous (ocPulse D.α D.q D.Λ D.ζ k pk) :=
    AVRegularity.CycleReference.ocPulse_continuous hζ pk
  rw [contDiff_one_iff_deriv]
  have hd : ∀ u, HasDerivAt (fun u : ℝ => ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v)
      (ocPulse D.α D.q D.Λ D.ζ k pk u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  refine ⟨fun u => (hd u).differentiableAt, ?_⟩
  have : deriv (fun u : ℝ => ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v) =
      ocPulse D.α D.q D.Λ D.ζ k pk := funext fun u => (hd u).deriv
  rw [this]; exact hc

theorem geomJacC1_base (D : OCData) (k : ℕ) (x : Vec 2) (s : ℝ) :
    GeomJacC1 (D.flowOf k, x, s) := by
  intro r
  have h := AVRegularity.CycleReference.streamFlow_joint_smooth (D.hΦ k)
  have hd : ContDiff ℝ 1 (fderiv ℝ (fun p : ℝ × Vec 2 × ℝ =>
      AVRegularity.streamFlow (D.Φ k) (D.hΦ k) p.1 p.2.1 p.2.2)) :=
    (h.fderiv_right (m := 1) (by simp)).of_le le_rfl
  let L : Vec 2 →L[ℝ] ℝ × Vec 2 × ℝ := ContinuousLinearMap.prod 0 (ContinuousLinearMap.prod
    (ContinuousLinearMap.id ℝ (Vec 2)) 0)
  have key : (fun p : ℝ × Vec 2 => fderiv ℝ (fun y => (D.flowOf k, x, s).1 p.1 y r) p.2) =
      fun p => (fderiv ℝ (fun q : ℝ × Vec 2 × ℝ =>
        AVRegularity.streamFlow (D.Φ k) (D.hΦ k) q.1 q.2.1 q.2.2) (p.1, p.2, r)).comp L := by
    funext p
    have h1 : HasFDerivAt (fun y : Vec 2 => ((p.1, y, r) : ℝ × Vec 2 × ℝ)) L p.2 :=
      (hasFDerivAt_const p.1 p.2).prodMk ((hasFDerivAt_id p.2).prodMk (hasFDerivAt_const r p.2))
    have h2 := (h.differentiable (by simp)) (p.1, p.2, r)
    exact (h2.hasFDerivAt.comp p.2 h1).fderiv
  rw [key]
  exact (hd.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))).clm_comp
    contDiff_const

theorem geomJacC1_childGeom (D : OCData) (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (s' : ℝ)
    (c : ChainChild) {g : ChainGeom} (hs : GeomSpatialSmooth g) (hg : GeomJacC1 g) :
    GeomJacC1 (D.childGeom k pk s' c g) := by
  intro r
  set A : Vec 2 → Vec 2 := fun x => g.1 g.2.2 x r with hAdef
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := hs g.2.2 r
  set γ : Vec 2 := c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center) with hγ
  set W : Vec 2 → Vec 2 := fun x =>
    ocShearVel D.α D.q D.Λ k pk (D.eps k • ((D.eps k)⁻¹ • A x + γ)) with hW
  have hWs : ContDiff ℝ (⊤ : ℕ∞) W :=
    (ocShearVel_spatial_smooth _ _ _ _ _).comp
      (((hA.const_smul _).add contDiff_const).const_smul _)
  set κ : ℝ → ℝ := fun u => D.eps k * ((D.eps k)⁻¹ *
    ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v) with hκ
  have hκc : ContDiff ℝ 1 κ :=
    contDiff_const.mul (contDiff_const.mul (contDiff_pulseIntegral D hζ k pk r))
  set Z : ℝ → Vec 2 → Vec 2 := fun u x => A x + κ u • W x with hZ
  have hZeq : ∀ u x, A x + D.eps k • D.relDisp k pk u r ((D.eps k)⁻¹ • A x + γ) = Z u x := by
    intro u x
    simp only [hZ, hκ, hW, OCData.relDisp, smul_smul]
  have hflow : (fun p : ℝ × Vec 2 =>
      fderiv ℝ (fun y => (D.childGeom k pk s' c g).1 p.1 y r) p.2) =
      fun p => (fderiv ℝ (fun y => g.1 p.1 y g.2.2) (Z p.1 p.2)).comp
        (fderiv ℝ A p.2 + κ p.1 • fderiv ℝ W p.2) := by
    funext p
    have hWd : DifferentiableAt ℝ W p.2 := hWs.differentiable (by simp) _
    have hKd : DifferentiableAt ℝ (fun x => κ p.1 • W x) p.2 := hWd.fun_const_smul (κ p.1)
    have hZd : DifferentiableAt ℝ (Z p.1) p.2 := (hA.differentiable (by simp) _).add hKd
    have hfd : fderiv ℝ (Z p.1) p.2 = fderiv ℝ A p.2 + κ p.1 • fderiv ℝ W p.2 := by
      change fderiv ℝ (fun x => A x + κ p.1 • W x) p.2 = _
      rw [fderiv_fun_add (hA.differentiable (by simp) _) hKd, fderiv_fun_const_smul hWd]
    have hfun : (fun y => (D.childGeom k pk s' c g).1 p.1 y r) =
        fun y => g.1 p.1 (Z p.1 y) g.2.2 := by
      funext y
      simp only [OCData.childGeom]
      rw [hZeq]
    rw [hfun, ← hfd]
    exact fderiv_comp p.2 ((hs p.1 g.2.2).differentiable (by simp) _) hZd
  rw [hflow]
  have hZj : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => Z p.1 p.2) := by
    have hA1 : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => A p.2) := (hA.of_le (by simp)).comp contDiff_snd
    have hW1 : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => W p.2) := (hWs.of_le (by simp)).comp contDiff_snd
    exact hA1.add ((hκc.comp contDiff_fst).smul hW1)
  have hGc := (hg g.2.2).comp (contDiff_fst.prodMk hZj)
  have hdA : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => fderiv ℝ A p.2) :=
    ((hA.fderiv_right (m := 1) (by simp)).of_le le_rfl).comp contDiff_snd
  have hdW : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => fderiv ℝ W p.2) :=
    ((hWs.fderiv_right (m := 1) (by simp)).of_le le_rfl).comp contDiff_snd
  exact hGc.clm_comp (hdA.add ((hκc.comp contDiff_fst).smul hdW))

theorem geomJacC1_geomAux (D : OCData) (hζ : IsFastProfile D.ζ) :
    ∀ (cs : List ChainChild) (k : ℕ) (sl : List ℤ) {g : ChainGeom},
      GeomSpatialSmooth g → GeomJacC1 g → GeomJacC1 (D.geomAux k sl cs g)
  | [], k, sl, g, _, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | _ :: _ :: _ => exact hg
  | c :: cs, k, sl, g, hs, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | pk :: pk1 :: rest =>
      exact geomJacC1_geomAux D hζ cs (k + 1) (pk1 :: rest)
        (geomSpatialSmooth_childGeom D k pk _ c hs) (geomJacC1_childGeom D hζ k pk _ c hs hg)

/-- **The spatial Jacobian of a chain geometry is jointly `C¹`.** -/
theorem geomJacC1_geom (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) :
    GeomJacC1 (ch.geom D) :=
  geomJacC1_geomAux D hζ _ _ _
    (fun _ _ => (CycleReference.streamFlow_joint_smooth (D.hΦ ch.baseLevel)).comp
      (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)))
    (geomJacC1_base D _ _ _)

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.CycleReference
namespace AVRegularity.Providers.GenSem

/-! Matrix algebra of a shear velocity `V` that is smooth and satisfies
`V(y + c V(y')) = V(y)` (`ocShearVel`, `ChainGeometry.ocShearVel_add_smul_self`): its Jacobian is
unchanged by such shifts and is square-zero, so `1 + c DV` is invertible with inverse
`1 - c DV`. Also the Jacobian of compositions and of a map with a nonsingular inverse. -/

section
section Shear

variable {V : Vec 2 → Vec 2}

theorem jacMatrix_shear_shift (hV : ∀ y y' (c : ℝ), V (y + c • V y') = V y) (y y' : Vec 2)
    (c : ℝ) : jacMatrix V (y + c • V y') = jacMatrix V y := by
  have h : (fun z => V (z + c • V y')) = V := funext fun z => hV z y' c
  have h2 : fderiv ℝ (fun z => V (z + c • V y')) y = fderiv ℝ V (y + c • V y') :=
    fderiv_comp_add_right (c • V y')
  rw [h] at h2
  unfold jacMatrix
  rw [← h2]

theorem jacMatrix_shear_sq (hV : ∀ y y' (c : ℝ), V (y + c • V y') = V y)
    (hd : Differentiable ℝ V) (y : Vec 2) : jacMatrix V y * jacMatrix V y = 0 := by
  set y0 := y - V y with hy0
  have hg : DifferentiableAt ℝ (fun z => y0 + V z) y := (hd y).const_add y0
  have hshift : y0 + V y = y := by simp [hy0]
  have hcomp : (V ∘ fun z => y0 + V z) = fun _ => V y0 := by
    funext z; simpa using hV y0 z 1
  have h1 := jacMatrix_comp (f := V) (g := fun z => y0 + V z) y
    (by simpa [hshift] using hd.differentiableAt) hg
  rw [hcomp] at h1
  have h2 : jacMatrix (fun z => y0 + V z) y = jacMatrix V y := by
    unfold jacMatrix; rw [fderiv_const_add]
  have h3 : jacMatrix (fun _ : Vec 2 => V y0) y = 0 := by
    ext i j; simp [jacMatrix]
  rw [h3, h2] at h1
  simp only [hshift] at h1
  exact h1.symm

end Shear

/-- The Jacobian of `y ↦ y + c V(y + w)`. -/
theorem jacMatrix_id_add_smul {V : Vec 2 → Vec 2} (hd : Differentiable ℝ V) (c : ℝ) (w y : Vec 2) :
    jacMatrix (fun z => z + c • V (z + w)) y = 1 + c • jacMatrix V (y + w) := by
  have hV : DifferentiableAt ℝ (fun z => V (z + w)) y :=
    (hd (y + w)).comp y ((differentiableAt_id).add_const w)
  have h1 : fderiv ℝ (fun z => V (z + w)) y = fderiv ℝ V (y + w) := fderiv_comp_add_right w
  have h2 : fderiv ℝ (fun z => z + c • V (z + w)) y =
      ContinuousLinearMap.id ℝ (Vec 2) + c • fderiv ℝ V (y + w) := by
    have := ((hasFDerivAt_id y).add (hV.hasFDerivAt.const_smul c)).fderiv
    rw [h1] at this
    exact this
  ext i j
  simp only [jacMatrix, Matrix.of_apply, h2, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, basisVec, smul_eq_mul]
  simp [Pi.single_apply]

/-- A map with a differentiable two-sided inverse has an invertible Jacobian. -/
theorem isUnit_det_jacMatrix {f f' : Vec 2 → Vec 2} (y : Vec 2) (hf : DifferentiableAt ℝ f y)
    (hf' : DifferentiableAt ℝ f' (f y)) (h : ∀ z, f' (f z) = z) :
    IsUnit (jacMatrix f y).det := by
  have h1 := jacMatrix_comp (f := f') (g := f) y hf' hf
  have h2 : (f' ∘ f) = id := funext h
  rw [h2, jacMatrix_identity] at h1
  exact Matrix.isUnit_det_of_left_inverse h1.symm
end

/-! Abstract core of the strain computation: the `u`-derivative of the Jacobian at a point `x'`
of the composite flow `X(u, Y(x) + P(u) V(Y(x) + w))`.

With `a = Y x'`, `v = V(a + w)`, `N = DV(a + w)`, `B = DY(x')`, `T(u) = a + P(u) v`, the Jacobian is
`F'(u) = DX(u, T u) · (B + P(u) N B)`, and when `X` has a spatial Jacobian that is differentiable
at `(t, T t)` its derivative at `t` is
`(∂_u DX + D_y DX[P'(t) v]) (1 + P N) B + DX (P' N B)`. -/

/-- The Jacobian of the composite at `x'`. -/
theorem jacComp_eq {X : ℝ → Vec 2 → Vec 2} {P : ℝ → ℝ} (hXd : ∀ u, Differentiable ℝ (X u))
    {Y V : Vec 2 → Vec 2} (hYd : Differentiable ℝ Y) (hVd : Differentiable ℝ V)
    (w x' : Vec 2) (u : ℝ) :
    jacMatrix (fun x => X u (Y x + P u • V (Y x + w))) x' =
      jacMatrix (X u) (Y x' + P u • V (Y x' + w)) *
        (jacMatrix Y x' + P u • (jacMatrix V (Y x' + w) * jacMatrix Y x')) := by
  have hZ : (fun x => X u (Y x + P u • V (Y x + w))) =
      X u ∘ ((fun z => z + P u • V (z + w)) ∘ Y) := rfl
  have hV1 : DifferentiableAt ℝ (fun z => V (z + w)) (Y x') :=
    (hVd (Y x' + w)).comp (Y x') (differentiableAt_id.add_const w)
  have hH : DifferentiableAt ℝ (fun z => z + P u • V (z + w)) (Y x') :=
    differentiableAt_id.add (hV1.const_smul (P u))
  rw [hZ, jacMatrix_comp x' ((hXd u) _) (hH.comp x' (hYd x')),
    jacMatrix_comp x' hH (hYd x'), jacMatrix_id_add_smul hVd]
  simp only [add_mul, one_mul, smul_mul_assoc]
  rfl

theorem jacComp_deriv_core {X : ℝ → Vec 2 → Vec 2} (hXd : ∀ u, Differentiable ℝ (X u))
    {Y V : Vec 2 → Vec 2} (hYd : Differentiable ℝ Y) (hVd : Differentiable ℝ V)
    {P : ℝ → ℝ} {p t : ℝ} (hP : HasDerivAt P p t) (w x' xA : Vec 2)
    (hT : Y x' + P t • V (Y x' + w) = xA)
    (hG : DifferentiableAt ℝ (fun q : ℝ × Vec 2 => fderiv ℝ (X q.1) q.2) (t, xA)) :
    Matrix.of (fun a b => deriv
        (fun u => jacMatrix (fun x => X u (Y x + P u • V (Y x + w))) x' a b) t) =
      (Matrix.of (fun a c => deriv (fun u => jacMatrix (X u) xA a c) t) +
        Matrix.of (fun a c => fderiv ℝ (fun y => jacMatrix (X t) y a c) xA
          (p • V (Y x' + w)))) *
        (jacMatrix Y x' + P t • (jacMatrix V (Y x' + w) * jacMatrix Y x')) +
      jacMatrix (X t) xA * (p • (jacMatrix V (Y x' + w) * jacMatrix Y x')) := by
  set a := Y x' with ha
  set v := V (a + w) with hv
  set N := jacMatrix V (a + w) with hN
  set B := jacMatrix Y x' with hB
  set T : ℝ → Vec 2 := fun u => a + P u • v with hTdef
  have hTt : T t = xA := hT
  have hT' : HasDerivAt T (p • v) t := (hP.smul_const v).const_add a
  have hjac : ∀ u, jacMatrix (fun x => X u (Y x + P u • V (Y x + w))) x' =
      jacMatrix (X u) (T u) * (B + P u • (N * B)) := fun u => jacComp_eq hXd hYd hVd w x' u
  have hφ : ∀ a' c, DifferentiableAt ℝ (fun q : ℝ × Vec 2 => jacMatrix (X q.1) q.2 a' c)
      (t, xA) := by
    intro a' c
    have h1 := hG.clm_apply (differentiableAt_const (basisVec c))
    exact (differentiableAt_pi.1 h1) a'
  have hent : ∀ a' c, HasDerivAt (fun u => jacMatrix (X u) (T u) a' c)
      (deriv (fun u => jacMatrix (X u) xA a' c) t +
        fderiv ℝ (fun y => jacMatrix (X t) y a' c) xA (p • v)) t := by
    intro a' c
    set φ : ℝ × Vec 2 → ℝ := fun q => jacMatrix (X q.1) q.2 a' c with hφdef
    have hφd : DifferentiableAt ℝ φ (t, xA) := hφ a' c
    have hφd' : DifferentiableAt ℝ φ (t, T t) := by rw [hTt]; exact hφd
    have hc := hφd'.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hT')
    have e1 : deriv (fun u => jacMatrix (X u) xA a' c) t = fderiv ℝ φ (t, xA) (1, 0) := by
      have h := (hφd.hasFDerivAt).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t xA))
      exact h.deriv
    have e2 : fderiv ℝ (fun y => jacMatrix (X t) y a' c) xA (p • v) =
        fderiv ℝ φ (t, xA) (0, p • v) := by
      have h1 : HasFDerivAt (fun y : Vec 2 => ((t, y) : ℝ × Vec 2))
          ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))) xA :=
        (hasFDerivAt_const t xA).prodMk (hasFDerivAt_id xA)
      have h := (hφd.hasFDerivAt).comp xA h1
      have h2 : HasFDerivAt (fun y => jacMatrix (X t) y a' c) _ xA := h
      rw [h2.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        zero_apply, ContinuousLinearMap.id_apply]
    rw [e1, e2, ← map_add]
    rw [hTt] at hc
    have e3 : ((1 : ℝ), (0 : Vec 2)) + (0, p • v) = (1, p • v) := by simp
    rw [e3]
    exact hc
  have hK : ∀ c b, HasDerivAt (fun u => (B + P u • (N * B)) c b) (p * (N * B) c b) t := by
    intro c b
    have := ((hP.mul_const ((N * B) c b)).const_add (B c b))
    simpa using this
  ext a' b
  rw [Matrix.of_apply]
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun c _ =>
    (hent a' c).mul (hK c b))
  have hfun : (fun u => jacMatrix (fun x => X u (Y x + P u • V (Y x + w))) x' a' b) =
      fun u => ∑ c : Fin 2, jacMatrix (X u) (T u) a' c * (B + P u • (N * B)) c b := by
    funext u; rw [hjac u, Matrix.mul_apply]
  rw [hfun]
  have hsum' : HasDerivAt (fun u => ∑ c : Fin 2, jacMatrix (X u) (T u) a' c *
      (B + P u • (N * B)) c b) (∑ c : Fin 2, ((deriv (fun u => jacMatrix (X u) xA a' c) t +
        fderiv ℝ (fun y => jacMatrix (X t) y a' c) xA (p • v)) * (B + P t • (N * B)) c b +
        jacMatrix (X t) xA a' c * (p * (N * B) c b))) t := by
    simpa [hTt] using hsum
  rw [hsum'.deriv]
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, smul_eq_mul]
  ring

end AVRegularity.Providers.GenSem
end
end

section
/-! The context strain of the first source equals the strain letter of the appended
child. For every finer slot `p'`,
`contextStrain D i pc t ch ζ = (ch.appendChild D p' t ζ).famStrain D t`
with `i = ch.ctxLevel`, `pc = ch.slot`: the anchor `s_{p'}` of the child drops out of the
Eulerian velocity gradient. -/

@[expose] public noncomputable section

open Homogenization AVenhance AVRegularity AVRegularity.CycleReference
  AVRegularity.EntryWeakProofs

namespace AVRegularity.Providers.GenSem

theorem eps_ne_zero (D : OCData) (hΛ : 1 ≤ D.Λ) (k : ℕ) : D.eps k ≠ 0 :=
  (AVRegularity.Construction.Stream.ocEpsilon_pos (q := D.q) (n := k) hΛ).ne'

/-- Matrix algebra of the strain: with `N² = 0`, `K = B + P N B`, `B`, `F` invertible. -/
theorem strain_algebra {F B N Dm : Matrix (Fin 2) (Fin 2) ℝ} (P p : ℝ)
    (hB : IsUnit B.det) (hNN : N * N = 0) :
    (Dm * (B + P • (N * B)) + F * (p • (N * B))) * (F * (B + P • (N * B)))⁻¹ =
      (Dm + F * (p • N)) * F⁻¹ := by
  set K := B + P • (N * B) with hKdef
  have hKe : K = (1 + P • N) * B := by
    simp [hKdef, add_mul]
  have hK : IsUnit K.det := by
    refine Matrix.isUnit_det_of_right_inverse (B := B⁻¹ * (1 - P • N)) ?_
    have hB1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
    have key : ∀ a : Matrix (Fin 2) (Fin 2) ℝ, a * a = 0 → (1 + a) * (1 - a) = 1 := by
      intro a ha
      calc (1 + a) * (1 - a) = 1 - a * a := by noncomm_ring
        _ = 1 := by rw [ha, sub_zero]
    have h2 : (1 + P • N) * (1 - P • N) = 1 :=
      key _ (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hNN, smul_zero])
    rw [hKe, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB1, Matrix.one_mul, h2]
  have hNK : N * K = N * B := by
    rw [hKdef, mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, hNN, Matrix.zero_mul, smul_zero,
      add_zero]
  have h1 : Dm * K + F * (p • (N * B)) = (Dm + F * (p • N)) * K := by
    rw [add_mul, Matrix.mul_assoc F, Matrix.smul_mul, hNK]
  rw [h1, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc K, Matrix.mul_nonsing_inv K hK,
    Matrix.one_mul]

/-- The appended chain's geometry is the child of the last family. -/
theorem appendChild_geom (D : OCData) (ch : RealChain) (hl : ch.WellSlotted) (p' : ℤ) (t : ℝ)
    (ζ : Vec 2) :
    (ch.appendChild D p' t ζ).geom D =
      D.childGeom ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) p')
        ⟨D.eps ch.ctxLevel • D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) p') t ζ,
          ζ + D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) p') t ζ⟩
        (ch.geom D) := by
  have hlen : ch.slots.length = ch.children.length + 1 := hl
  simp only [RealChain.geom, RealChain.appendChild]
  rw [ChainGeometry.geomAux_append D _ _ ch.children _ ch.slots _ hlen]
  have hhead : (ch.slots ++ [p']).headD 0 = ch.slots.headD 0 := by
    cases h : ch.slots with
    | nil => rw [h] at hlen; simp at hlen
    | cons a l => rfl
  have hL : ch.ctxLevel = ch.baseLevel + 1 + ch.children.length := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel]; omega
  rw [hhead, hL]
  rfl

/-- The flow of the appended child, in the form `X(u, Y x + P(u) V(Y x + w))`. -/
theorem childGeom_flow_eq (D : OCData) (k : ℕ) (pk : ℤ) (hε : D.eps k ≠ 0) (s' : ℝ)
    (g : ChainGeom) (d ζ : Vec 2) (u r : ℝ) (y : Vec 2) :
    (D.childGeom k pk s' ⟨D.eps k • d, ζ + d⟩ g).1 u y r =
      g.1 u (g.1 g.2.2 y r + (∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v) •
        ocShearVel D.α D.q D.Λ k pk (g.1 g.2.2 y r + (D.eps k • ζ - g.2.1))) g.2.2 := by
  simp only [OCData.childGeom, OCData.relDisp]
  rw [smul_inv_smul₀ hε]
  simp only [smul_add, smul_sub, smul_inv_smul₀ hε]
  abel_nf

theorem jacMatrix_labelShear (D : OCData) (k : ℕ) (pk : ℤ) (t : ℝ) (ζ : Vec 2) :
    jacMatrix (labelShear D k pk t) ζ =
      (ocPulse D.α D.q D.Λ D.ζ k pk t * D.eps k) •
        jacMatrix (ocShearVel D.α D.q D.Λ k pk) (D.eps k • ζ) := by
  have hd : Differentiable ℝ (ocShearVel D.α D.q D.Λ k pk) :=
    (ocShearVel_spatial_smooth _ _ _ _ _).differentiable (by simp)
  have h0 := (((hd _).hasFDerivAt.comp ζ ((hasFDerivAt_id ζ).const_smul (D.eps k))).const_smul
    (ocPulse D.α D.q D.Λ D.ζ k pk t))
  have h : HasFDerivAt (labelShear D k pk t) _ ζ := h0
  ext i j
  simp only [jacMatrix, Matrix.of_apply, h.fderiv, Matrix.smul_apply, smul_eq_mul]
  simp
  ring

theorem contextStrain_eq_childStrain (D : OCData) (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ)
    (ch : RealChain) (hl : ch.WellSlotted) (p' : ℤ) (t : ℝ) (ζ : Vec 2) :
    contextStrain D ch.ctxLevel ch.slot t ch ζ = (ch.appendChild D p' t ζ).famStrain D t := by
  have hε := eps_ne_zero D hΛ ch.ctxLevel
  have hflow := isFlowGeom_geom D hζ ch
  have happ := appendChild_geom D ch hl p' t ζ
  set g := ch.geom D with hg
  set k := ch.ctxLevel with hk
  set pk := ch.slot with hpk
  set s' := D.slotAnchor (k + 1) p' with hs'
  set ε := D.eps k with hεdef
  set V := ocShearVel D.α D.q D.Λ k pk with hV
  set pf := ocPulse D.α D.q D.Λ D.ζ k pk with hpf
  set d := D.relDisp k pk s' t ζ with hd
  set c := ε • d with hcdef
  set m := ∫ v in t..s', pf v with hm
  set X : ℝ → Vec 2 → Vec 2 := fun u y => g.1 u y g.2.2 with hX
  set Y : Vec 2 → Vec 2 := fun y => g.1 g.2.2 y s' with hY
  set P : ℝ → ℝ := fun u => ∫ v in s'..u, pf v with hP
  set w : Vec 2 := ε • ζ - g.2.1 with hw
  set x' : Vec 2 := g.1 s' (g.2.1 + c) g.2.2 with hx'
  have hVprop : ∀ y y' (c : ℝ), V (y + c • V y') = V y :=
    fun y y' c => ChainGeometry.ocShearVel_add_smul_self _ _ _ _ _ y y' c
  have hVd : Differentiable ℝ V := (ocShearVel_spatial_smooth _ _ _ _ _).differentiable (by simp)
  have hXd : ∀ u, Differentiable ℝ (X u) := fun u =>
    (geomSpatialSmooth_geom D ch u g.2.2).differentiable (by simp)
  have hYd : Differentiable ℝ Y :=
    (geomSpatialSmooth_geom D ch g.2.2 s').differentiable (by simp)
  have hG : DifferentiableAt ℝ (fun q : ℝ × Vec 2 => fderiv ℝ (X q.1) q.2) (t, g.2.1) :=
    ((geomJacC1_geom D hζ ch g.2.2).differentiable (by simp)) (t, g.2.1)
  have hpc : Continuous pf := CycleReference.ocPulse_continuous hζ pk
  have hPd : HasDerivAt P (pf t) t :=
    intervalIntegral.integral_hasDerivAt_right (hpc.intervalIntegrable _ _)
      (hpc.stronglyMeasurableAtFilter _ _) hpc.continuousAt
  -- the displacement
  have hc : c = m • V (ε • ζ) := by
    simp only [hcdef, hd, OCData.relDisp, hm, hV, hpf, hεdef]
    rw [smul_inv_smul₀ hε]
  have hYx : Y x' = g.2.1 + c := hflow.inv g.2.2 s' _
  have hYw : Y x' + w = ε • ζ + m • V (ε • ζ) := by
    rw [hYx, hw, hc]; abel
  have hVw : V (Y x' + w) = V (ε • ζ) := by rw [hYw]; exact hVprop _ _ _
  have hNw : jacMatrix V (Y x' + w) = jacMatrix V (ε • ζ) := by
    rw [hYw]; exact jacMatrix_shear_shift hVprop _ _ _
  have hPt : P t = -m := by
    simp only [hP, hm]; rw [intervalIntegral.integral_symm]
  have hT : Y x' + P t • V (Y x' + w) = g.2.1 := by
    rw [hVw, hPt, hYx, hc, neg_smul]; abel
  -- the Jacobians of the appended chain
  have hfam : ∀ u, (ch.appendChild D p' t ζ).famJac D u =
      jacMatrix (fun x => X u (Y x + P u • V (Y x + w))) x' := by
    intro u
    rw [RealChain.famJac, happ]
    show jacMatrix (fun y => (D.childGeom k pk s' ⟨ε • d, ζ + d⟩ g).1 u y s') x' = _
    congr 1
    funext y
    exact childGeom_flow_eq D k pk hε s' g d ζ u s' y
  have hcore := jacComp_deriv_core hXd hYd hVd hPd w x' g.2.1 hT hG
  have hFp : (ch.appendChild D p' t ζ).famJac D t =
      jacMatrix (X t) g.2.1 * (jacMatrix Y x' + P t • (jacMatrix V (Y x' + w) * jacMatrix Y x')) := by
    rw [hfam, jacComp_eq hXd hYd hVd w x' t, hT]
  have hstr : (ch.appendChild D p' t ζ).famStrain D t =
      Matrix.of (fun a b => deriv (fun u => jacMatrix (fun x => X u (Y x + P u • V (Y x + w))) x' a b) t) *
        ((ch.appendChild D p' t ζ).famJac D t)⁻¹ := by
    simp only [RealChain.famStrain, hfam]
  rw [hstr, hFp, hcore]
  -- invertibility
  have hFu : IsUnit (jacMatrix (X t) g.2.1).det :=
    isUnit_det_jacMatrix g.2.1 ((hXd t) _)
      (((geomSpatialSmooth_geom D ch g.2.2 t).differentiable (by simp)) _)
      (fun z => hflow.inv g.2.2 t z)
  have hBu : IsUnit (jacMatrix Y x').det :=
    isUnit_det_jacMatrix x' (hYd _)
      (((geomSpatialSmooth_geom D ch s' g.2.2).differentiable (by simp)) _)
      (fun z => hflow.inv s' g.2.2 z)
  have hNN : jacMatrix V (Y x' + w) * jacMatrix V (Y x' + w) = 0 := by
    rw [hNw]; exact jacMatrix_shear_sq hVprop hVd _
  rw [strain_algebra (P t) (pf t) hBu hNN]
  -- the context strain
  have hF : ch.famJac D t = jacMatrix (X t) g.2.1 := rfl
  have hstr0 : ch.famStrain D t = Matrix.of (fun a c => deriv (fun u => jacMatrix (X u) g.2.1 a c) t) *
      (jacMatrix (X t) g.2.1)⁻¹ := rfl
  have hDU : Matrix.of (fun a c => fderiv ℝ (fun h : Vec 2 => (ch.recenter D h).famJac D t a c) 0
        (labelShear D k pk t ζ)) =
      Matrix.of (fun a c => fderiv ℝ (fun y => jacMatrix (X t) y a c) g.2.1
        (pf t • V (Y x' + w))) := by
    ext a c'
    simp only [Matrix.of_apply]
    have hfun : (fun h : Vec 2 => (ch.recenter D h).famJac D t a c') =
        fun h => (fun y => jacMatrix (X t) y a c') (g.2.1 + h) := by
      funext h; rw [famJac_recenter D hζ ch hl]
    have e := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y => jacMatrix (X t) y a c') (x := (0 : Vec 2)) g.2.1
    rw [hfun, e, add_zero, hVw]
    rfl
  have hlab : ε⁻¹ • jacMatrix (labelShear D k pk t) ζ = pf t • jacMatrix V (Y x' + w) := by
    rw [jacMatrix_labelShear, hNw, smul_smul]
    have : ε⁻¹ * (pf t * ε) = pf t := by field_simp
    rw [this]
  unfold contextStrain
  rw [hstr0, hDU, hlab, hF]
  simp only [add_mul, add_assoc]

end AVRegularity.Providers.GenSem
end
end
