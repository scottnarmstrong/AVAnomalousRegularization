-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.SuccessorGeneration.Setup
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization
open scoped Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **Complex strips of the plane.** Complex vectors `z ∈ ℂ²` (`CVec`) with the `ℓ¹`
norm `|z|₁ = |z₁| + |z₂|` (`l1`) and the `ℓ¹` norm of the imaginary part (`imL1`); the strips
`S_ℓ = {|Im z|₁ < ℓ}` (`strip`) and their closures (`cstrip`), as in the paragraph before
Proposition 6.5 of the paper. The real points `ofRealVec x`, the real part `reVec`.
* `retract ℓ'`: the retraction onto the closed strip `S̄_{ℓ'}` that scales the imaginary part
  down to `|Im|₁ ≤ ℓ'` and keeps the real part; continuous, the identity on `S̄_{ℓ'}`, real on
  real points.
* `l1_integral_le`, `imL1_integral_le`: the `ℓ¹` norms of an interval integral are bounded by the
  integrals of the `ℓ¹` norms over `Ι a b`. -/

/-- Complex vectors of the plane. -/
abbrev CVec : Type := Fin 2 → ℂ

/-- The `ℓ¹` norm `|z|₁`. -/
def l1 (z : CVec) : ℝ := ∑ a, ‖z a‖

/-- The `ℓ¹` norm of the imaginary part `|Im z|₁`. -/
def imL1 (z : CVec) : ℝ := ∑ a, |(z a).im|

/-- The open strip `S_ℓ = {|Im z|₁ < ℓ}`. -/
def strip (ℓ : ℝ) : Set CVec := {z | imL1 z < ℓ}

/-- The closed strip `S̄_ℓ = {|Im z|₁ ≤ ℓ}`. -/
def cstrip (ℓ : ℝ) : Set CVec := {z | imL1 z ≤ ℓ}

/-- The real point `x ∈ ℝ²` as a complex vector. -/
def ofRealVec (x : Vec 2) : CVec := fun a => (x a : ℂ)

/-- The real part of a complex vector. -/
def reVec (z : CVec) : Vec 2 := fun a => (z a).re

/-! ### Norms -/

theorem l1_nonneg (z : CVec) : 0 ≤ l1 z := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem imL1_nonneg (z : CVec) : 0 ≤ imL1 z := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem l1_add_le (z w : CVec) : l1 (z + w) ≤ l1 z + l1 w := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => norm_add_le _ _

theorem l1_zero : l1 0 = 0 := by simp [l1]

theorem imL1_le_l1 (z : CVec) : imL1 z ≤ l1 z :=
  Finset.sum_le_sum fun _ _ => Complex.abs_im_le_norm _

theorem imL1_add_le (z w : CVec) : imL1 (z + w) ≤ imL1 z + imL1 w := by
  unfold imL1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ => by simpa using abs_add_le _ _

theorem imL1_le_add_l1 (z w : CVec) : imL1 z ≤ imL1 w + l1 (z - w) := by
  have h := imL1_add_le w (z - w)
  rw [add_sub_cancel] at h
  exact h.trans (add_le_add le_rfl (imL1_le_l1 _))

theorem norm_le_l1 (z : CVec) : ‖z‖ ≤ l1 z := by
  refine (pi_norm_le_iff_of_nonneg (l1_nonneg z)).mpr fun a => ?_
  exact Finset.single_le_sum (f := fun a => ‖z a‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ a)

theorem l1_le_two_mul_norm (z : CVec) : l1 z ≤ 2 * ‖z‖ := by
  unfold l1
  rw [Fin.sum_univ_two, two_mul]
  exact add_le_add (norm_le_pi_norm z 0) (norm_le_pi_norm z 1)

theorem continuous_l1 : Continuous l1 := by
  unfold l1
  fun_prop

theorem continuous_imL1 : Continuous imL1 := by
  unfold imL1
  refine continuous_finsetSum _ fun a _ => ?_
  exact (Complex.continuous_im.comp (continuous_apply a)).abs

theorem imL1_ofRealVec (x : Vec 2) : imL1 (ofRealVec x) = 0 := by
  simp [imL1, ofRealVec]

/-- The imaginary part of `z` is the `ℓ¹` distance to its real part. -/
theorem l1_sub_ofRealVec_reVec (z : CVec) : l1 (z - ofRealVec (reVec z)) = imL1 z := by
  unfold l1 imL1
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : z a - ((z a).re : ℂ) = ((z a).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simp only [Pi.sub_apply, ofRealVec, reVec, e, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-! ### Strips -/

theorem isOpen_strip (ℓ : ℝ) : IsOpen (strip ℓ) :=
  isOpen_lt continuous_imL1 continuous_const

theorem isClosed_cstrip (ℓ : ℝ) : IsClosed (cstrip ℓ) :=
  isClosed_le continuous_imL1 continuous_const

theorem convex_cstrip (ℓ : ℝ) : Convex ℝ (cstrip ℓ) := by
  intro z hz w hw a b ha hb hab
  show imL1 (a • z + b • w) ≤ ℓ
  have h1 : imL1 (a • z + b • w) ≤ a * imL1 z + b * imL1 w := by
    unfold imL1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun c _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.real_smul,
      Complex.im_ofReal_mul]
    rw [← abs_of_nonneg ha, ← abs_of_nonneg hb, ← abs_mul, ← abs_mul, abs_of_nonneg ha,
      abs_of_nonneg hb]
    exact abs_add_le _ _
  have h2 : a * imL1 z + b * imL1 w ≤ a * ℓ + b * ℓ :=
    add_le_add (mul_le_mul_of_nonneg_left hz ha) (mul_le_mul_of_nonneg_left hw hb)
  rw [← add_mul, hab, one_mul] at h2
  exact h1.trans h2

theorem convex_strip (ℓ : ℝ) : Convex ℝ (strip ℓ) := by
  intro z hz w hw a b ha hb hab
  show imL1 (a • z + b • w) < ℓ
  have h1 : imL1 (a • z + b • w) ≤ a * imL1 z + b * imL1 w := by
    unfold imL1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun c _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.real_smul,
      Complex.im_ofReal_mul]
    rw [← abs_of_nonneg ha, ← abs_of_nonneg hb, ← abs_mul, ← abs_mul, abs_of_nonneg ha,
      abs_of_nonneg hb]
    exact abs_add_le _ _
  rcases ha.lt_or_eq with ha' | ha'
  · have h2 : a * imL1 z + b * imL1 w < a * ℓ + b * ℓ :=
      add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hz ha') (mul_le_mul_of_nonneg_left hw.le hb)
    rw [← add_mul, hab, one_mul] at h2
    exact h1.trans_lt h2
  · subst ha'
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa [strip] using hw

theorem cstrip_subset_strip {ℓ' ℓ : ℝ} (h : ℓ' < ℓ) : cstrip ℓ' ⊆ strip ℓ :=
  fun _ hz => lt_of_le_of_lt hz h

theorem strip_subset_cstrip (ℓ : ℝ) : strip ℓ ⊆ cstrip ℓ :=
  fun _ hz => le_of_lt (show _ < ℓ from hz)

theorem ofRealVec_mem_strip {ℓ : ℝ} (hℓ : 0 < ℓ) (x : Vec 2) : ofRealVec x ∈ strip ℓ := by
  show imL1 (ofRealVec x) < ℓ
  rw [imL1_ofRealVec]
  exact hℓ

/-! ### The retraction onto a closed strip -/

/-- The scale factor of the retraction: `1` on `S̄_{ℓ'}`, `ℓ'/|Im z|₁` outside. -/
def retractScale (ℓ' : ℝ) (z : CVec) : ℝ := ℓ' / max ℓ' (imL1 z)

/-- The retraction onto the closed strip `S̄_{ℓ'}`. -/
def retract (ℓ' : ℝ) (z : CVec) : CVec :=
  fun a => ((z a).re : ℂ) + ((retractScale ℓ' z * (z a).im : ℝ) : ℂ) * Complex.I

theorem retractScale_eq_one {ℓ' : ℝ} (hℓ : 0 < ℓ') {z : CVec} (hz : z ∈ cstrip ℓ') :
    retractScale ℓ' z = 1 := by
  unfold retractScale
  rw [max_eq_left hz, div_self hℓ.ne']

theorem retractScale_nonneg {ℓ' : ℝ} (hℓ : 0 < ℓ') (z : CVec) : 0 ≤ retractScale ℓ' z :=
  div_nonneg hℓ.le (hℓ.le.trans (le_max_left _ _))

theorem retract_eq_self {ℓ' : ℝ} (hℓ : 0 < ℓ') {z : CVec} (hz : z ∈ cstrip ℓ') :
    retract ℓ' z = z := by
  funext a
  simp only [retract, retractScale_eq_one hℓ hz, one_mul]
  exact Complex.re_add_im (z a)

theorem retract_mem_cstrip {ℓ' : ℝ} (hℓ : 0 < ℓ') (z : CVec) : retract ℓ' z ∈ cstrip ℓ' := by
  show imL1 (retract ℓ' z) ≤ ℓ'
  have e : imL1 (retract ℓ' z) = retractScale ℓ' z * imL1 z := by
    unfold imL1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [retract, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero, abs_mul,
      abs_of_nonneg (retractScale_nonneg hℓ z)]
  rw [e]
  unfold retractScale
  rw [div_mul_eq_mul_div, div_le_iff₀ (hℓ.trans_le (le_max_left _ _))]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hℓ.le

theorem continuous_retract {ℓ' : ℝ} (hℓ : 0 < ℓ') : Continuous (retract ℓ') := by
  have hs : Continuous (retractScale ℓ') := by
    unfold retractScale
    exact continuous_const.div (continuous_const.max continuous_imL1)
      fun z => (hℓ.trans_le (le_max_left _ _)).ne'
  unfold retract
  refine continuous_pi fun a => ?_
  have h1 : Continuous fun z : CVec => z a := continuous_apply a
  exact (Complex.continuous_ofReal.comp (Complex.continuous_re.comp h1)).add
    ((Complex.continuous_ofReal.comp (hs.mul (Complex.continuous_im.comp h1))).mul
      continuous_const)

/-! ### `ℓ¹` norms of interval integrals -/

theorem integral_apply_eq {f : ℝ → CVec} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (c : Fin 2) : (∫ x in a..b, f x) c = ∫ x in a..b, f x c :=
  ((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).intervalIntegral_comp_comm hf).symm

theorem l1_integral_le {f : ℝ → CVec} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    l1 (∫ x in a..b, f x) ≤ ∫ x in Ι a b, l1 (f x) := by
  have hc : ∀ c : Fin 2, Integrable (fun x => f x c) (volume.restrict (Ι a b)) :=
    fun c => (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).integrable_comp hf.def'
  unfold l1
  rw [integral_finsetSum _ fun c _ => (hc c).norm]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [integral_apply_eq hf c]
  exact intervalIntegral.norm_integral_le_integral_norm_uIoc

theorem imL1_integral_le {f : ℝ → CVec} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    imL1 (∫ x in a..b, f x) ≤ ∫ x in Ι a b, imL1 (f x) := by
  have hc : ∀ c : Fin 2, Integrable (fun x => (f x c).im) (volume.restrict (Ι a b)) :=
    fun c => (Complex.imCLM.comp (ContinuousLinearMap.proj c : CVec →L[ℝ] ℂ)).integrable_comp
      hf.def'
  unfold imL1
  rw [integral_finsetSum _ fun c _ => (hc c).abs]
  refine Finset.sum_le_sum fun c _ => ?_
  have e : (∫ x in a..b, f x) c = ∫ x in a..b, f x c := integral_apply_eq hf c
  have hci : IntervalIntegrable (fun x => f x c) volume a b :=
    ⟨(ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).integrable_comp hf.1,
      (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).integrable_comp hf.2⟩
  have e2 : (∫ x in a..b, f x c).im = ∫ x in a..b, (f x c).im :=
    (Complex.imCLM.intervalIntegral_comp_comm hci).symm
  rw [e, e2]
  have h := intervalIntegral.norm_integral_le_integral_norm_uIoc (a := a) (b := b)
    (μ := volume) (f := fun x => (f x c).im)
  simpa only [Real.norm_eq_abs] using h

/-- An integral over `Ι a b` of a function bounded by `C` is at most `C |b - a|`. -/
theorem setIntegral_uIoc_le_const {g : ℝ → ℝ} {a b C : ℝ} (hC : ∀ x ∈ Ι a b, g x ≤ C)
    (hg : ∀ x ∈ Ι a b, 0 ≤ g x) : ∫ x in Ι a b, g x ≤ C * |b - a| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := C)
    (f := g) fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg x hx)]
      exact hC x hx
  rw [intervalIntegral.norm_integral_eq_norm_integral_uIoc, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Homogenization
open scoped Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **Complex trajectories by Picard iteration**. A velocity field `v` on the strip `S_ℓ` that is
continuous, `Γ`-Lipschitz in
`|·|₁`, real on real points and bounded by `V` there (`StripField`) has, on a time window
`[a, b]` with `Γ(b - a) ≤ 2/5` and for a closed sub-strip `S̄_{ℓ'}`, `ℓ' < ℓ`, a flow `cflow`:
* the Picard iterates `pic n τ z s` of the field retracted onto `S̄_{ℓ'}` (`rf`) are jointly
  continuous in `(τ, z, s)` (`continuous_pic`);
* for `τ, s ∈ [a, b]` and `|Im z|₁ ≤ (1 - Γ(b-a)) ℓ'` (`Z0`) they stay in `S̄_{ℓ'}` (`pic_mem`),
  where the retracted field is the field, and they converge geometrically with ratio `Γ(b-a)`
  (`dist_pic_succ_le`);
* their limit `cflow` stays in `S̄_{ℓ'}`, solves the integral equation
  `X(τ) = z + ∫_s^τ v(σ, X(σ)) dσ` (`cflow_eq`), is jointly continuous on the window
  (`continuousOn_cflow`), and is real at real initial points.
The imaginary part is controlled by the Lipschitz bound alone: `|Im v(z)|₁ ≤ Γ|Im z|₁`
(`StripField.imL1_le`), since `v` is real at the real part of `z`. -/

/-- **The hypotheses on a velocity field on the strip `S_ℓ`.** -/
structure StripField (v : ℝ → CVec → CVec) (ℓ Γ V : ℝ) : Prop where
  /-- Joint continuity on `ℝ × S_ℓ`. -/
  cont : ContinuousOn (fun p : ℝ × CVec => v p.1 p.2) (univ ×ˢ strip ℓ)
  /-- The `|·|₁`-Lipschitz bound on `S_ℓ`. -/
  lip : ∀ t, ∀ z ∈ strip ℓ, ∀ w ∈ strip ℓ, l1 (v t z - v t w) ≤ Γ * l1 (z - w)
  /-- Real values at real points. -/
  real : ∀ t (x : Vec 2), imL1 (v t (ofRealVec x)) = 0
  /-- The bound at real points. -/
  bdd : ∀ t (x : Vec 2), l1 (v t (ofRealVec x)) ≤ V
  /-- The Lipschitz constant is nonnegative. -/
  hΓ : 0 ≤ Γ

/-- **The time window and the closed sub-strip of the flow.** -/
structure FlowWin (ℓ ℓ' Γ a b : ℝ) : Prop where
  hℓ' : 0 < ℓ'
  hℓℓ : ℓ' < ℓ
  hab : a ≤ b
  hΓT : Γ * (b - a) ≤ 2 / 5

/-- The admissible initial points: `|Im z|₁ ≤ (1 - Γ(b - a)) ℓ'`. -/
def Z0 (ℓ' Γ a b : ℝ) : Set CVec := cstrip ((1 - Γ * (b - a)) * ℓ')

variable {v : ℝ → CVec → CVec} {ℓ ℓ' Γ V a b : ℝ}

namespace StripField

theorem imL1_le (hv : StripField v ℓ Γ V) (hℓ : 0 < ℓ) (t : ℝ) {z : CVec} (hz : z ∈ strip ℓ) :
    imL1 (v t z) ≤ Γ * imL1 z := by
  have hx : ofRealVec (reVec z) ∈ strip ℓ := ofRealVec_mem_strip hℓ _
  have h1 := imL1_le_add_l1 (v t z) (v t (ofRealVec (reVec z)))
  rw [hv.real] at h1
  have h2 := hv.lip t z hz _ hx
  rw [l1_sub_ofRealVec_reVec] at h2
  linarith

theorem l1_le (hv : StripField v ℓ Γ V) (hℓ : 0 < ℓ) (t : ℝ) {z : CVec} (hz : z ∈ strip ℓ) :
    l1 (v t z) ≤ V + Γ * imL1 z := by
  have hx : ofRealVec (reVec z) ∈ strip ℓ := ofRealVec_mem_strip hℓ _
  have h1 : l1 (v t z) ≤ l1 (v t (ofRealVec (reVec z))) + l1 (v t z - v t (ofRealVec (reVec z))) := by
    have := l1_add_le (v t (ofRealVec (reVec z))) (v t z - v t (ofRealVec (reVec z)))
    rwa [add_sub_cancel] at this
  have h2 := hv.lip t z hz _ hx
  rw [l1_sub_ofRealVec_reVec] at h2
  linarith [hv.bdd t (reVec z)]

end StripField

/-! ### The retracted field -/

/-- The field retracted onto the closed strip `S̄_{ℓ'}`. -/
def rf (v : ℝ → CVec → CVec) (ℓ' : ℝ) (t : ℝ) (z : CVec) : CVec := v t (retract ℓ' z)

theorem rf_eq (hℓ' : 0 < ℓ') {t : ℝ} {z : CVec} (hz : z ∈ cstrip ℓ') : rf v ℓ' t z = v t z := by
  rw [rf, retract_eq_self hℓ' hz]

theorem continuous_rf (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) :
    Continuous (fun p : ℝ × CVec => rf v ℓ' p.1 p.2) := by
  have hc : Continuous fun p : ℝ × CVec => (p.1, retract ℓ' p.2) :=
    continuous_fst.prodMk ((continuous_retract hw.hℓ').comp continuous_snd)
  refine hv.cont.comp_continuous hc fun p => ?_
  exact ⟨mem_univ _, cstrip_subset_strip hw.hℓℓ (retract_mem_cstrip hw.hℓ' p.2)⟩

theorem l1_rf_le (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) (t : ℝ) (z : CVec) :
    l1 (rf v ℓ' t z) ≤ V + Γ * ℓ' := by
  have hm := retract_mem_cstrip hw.hℓ' z
  refine (hv.l1_le (hw.hℓ'.trans hw.hℓℓ) t (cstrip_subset_strip hw.hℓℓ hm)).trans ?_
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hm hv.hΓ)

/-! ### Picard iterates -/

/-- The Picard iterates of the retracted field, from `z` at the time `s`. -/
def pic (v : ℝ → CVec → CVec) (ℓ' : ℝ) : ℕ → ℝ → CVec → ℝ → CVec
  | 0 => fun _ z _ => z
  | n + 1 => fun τ z s => z + ∫ σ in s..τ, rf v ℓ' σ (pic v ℓ' n σ z s)

theorem pic_succ (n : ℕ) (τ : ℝ) (z : CVec) (s : ℝ) :
    pic v ℓ' (n + 1) τ z s = z + ∫ σ in s..τ, rf v ℓ' σ (pic v ℓ' n σ z s) := rfl

theorem continuous_pic (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) (n : ℕ) :
    Continuous (fun p : ℝ × CVec × ℝ => pic v ℓ' n p.1 p.2.1 p.2.2) := by
  induction n with
  | zero => exact continuous_snd.fst
  | succ n ih =>
    have hf : Continuous (fun q : (ℝ × CVec × ℝ) × ℝ =>
        rf v ℓ' q.2 (pic v ℓ' n q.2 q.1.2.1 q.1.2.2)) :=
      (continuous_rf hv hw).comp (continuous_snd.prodMk
        (ih.comp (continuous_snd.prodMk (continuous_fst.snd.fst.prodMk continuous_fst.snd.snd))))
    have h1 : Continuous fun p : ℝ × CVec × ℝ =>
        ∫ σ in (0 : ℝ)..p.1, rf v ℓ' σ (pic v ℓ' n σ p.2.1 p.2.2) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : ℝ × CVec × ℝ) σ => rf v ℓ' σ (pic v ℓ' n σ p.2.1 p.2.2)) hf continuous_fst
    have h2 : Continuous fun p : ℝ × CVec × ℝ =>
        ∫ σ in (0 : ℝ)..p.2.2, rf v ℓ' σ (pic v ℓ' n σ p.2.1 p.2.2) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : ℝ × CVec × ℝ) σ => rf v ℓ' σ (pic v ℓ' n σ p.2.1 p.2.2)) hf
        continuous_snd.snd
    have e : (fun p : ℝ × CVec × ℝ => pic v ℓ' (n + 1) p.1 p.2.1 p.2.2) = fun p =>
        p.2.1 + ((∫ σ in (0 : ℝ)..p.1, rf v ℓ' σ (pic v ℓ' n σ p.2.1 p.2.2)) -
          ∫ σ in (0 : ℝ)..p.2.2, rf v ℓ' σ (pic v ℓ' n σ p.2.1 p.2.2)) := by
      funext p
      rw [pic_succ, intervalIntegral.integral_interval_sub_left]
      · exact (hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      · exact (hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    rw [e]
    exact continuous_snd.fst.add (h1.sub h2)

theorem continuous_pic_time (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) (n : ℕ)
    (z : CVec) (s : ℝ) : Continuous fun σ => pic v ℓ' n σ z s :=
  (continuous_pic hv hw n).comp
    (continuous_id.prodMk continuous_const : Continuous fun σ : ℝ => (σ, z, s))

theorem intervalIntegrable_rf_pic (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) (n : ℕ)
    (z : CVec) (s τ₀ τ₁ : ℝ) :
    IntervalIntegrable (fun σ => rf v ℓ' σ (pic v ℓ' n σ z s)) volume τ₀ τ₁ :=
  ((continuous_rf hv hw).comp (continuous_id.prodMk (continuous_pic_time hv hw n z s))).intervalIntegrable
    _ _

theorem uIoc_subset_window {τ s : ℝ} (hτ : τ ∈ Icc a b) (hs : s ∈ Icc a b) : Ι s τ ⊆ Icc a b :=
  uIoc_subset_uIcc.trans (uIcc_subset_Icc hs hτ)

theorem abs_sub_le_window {τ s : ℝ} (hτ : τ ∈ Icc a b) (hs : s ∈ Icc a b) : |τ - s| ≤ b - a := by
  rw [abs_le]
  constructor <;> linarith [hτ.1, hτ.2, hs.1, hs.2]

/-- **The iterates stay in the closed sub-strip.** -/
theorem pic_mem (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) (n : ℕ) :
    ∀ τ ∈ Icc a b, pic v ℓ' n τ z s ∈ cstrip ℓ' := by
  have hℓ : 0 < ℓ := hw.hℓ'.trans hw.hℓℓ
  have hΓT0 : 0 ≤ Γ * (b - a) := mul_nonneg hv.hΓ (sub_nonneg.mpr hw.hab)
  have hz' : z ∈ cstrip ℓ' := by
    show imL1 z ≤ ℓ'
    have : imL1 z ≤ (1 - Γ * (b - a)) * ℓ' := hz
    nlinarith [hw.hℓ']
  induction n with
  | zero => exact fun _ _ => hz'
  | succ n ih =>
    intro τ hτ
    show imL1 (pic v ℓ' (n + 1) τ z s) ≤ ℓ'
    rw [pic_succ]
    have hint := imL1_integral_le (intervalIntegrable_rf_pic hv hw n z s s τ)
    have hbd : ∫ σ in Ι s τ, imL1 (rf v ℓ' σ (pic v ℓ' n σ z s)) ≤ (Γ * ℓ') * |τ - s| := by
      refine setIntegral_uIoc_le_const (fun σ hσ => ?_) (fun σ _ => imL1_nonneg _)
      have hm := ih σ (uIoc_subset_window hτ hs hσ)
      rw [rf_eq hw.hℓ' hm]
      exact (hv.imL1_le hℓ σ (cstrip_subset_strip hw.hℓℓ hm)).trans
        (mul_le_mul_of_nonneg_left hm hv.hΓ)
    have hT := abs_sub_le_window hτ hs
    have h3 : (Γ * ℓ') * |τ - s| ≤ Γ * (b - a) * ℓ' := by
      have := mul_le_mul_of_nonneg_left hT (mul_nonneg hv.hΓ hw.hℓ'.le)
      linarith
    have hz0 : imL1 z ≤ (1 - Γ * (b - a)) * ℓ' := hz
    linarith [imL1_add_le z (∫ σ in s..τ, rf v ℓ' σ (pic v ℓ' n σ z s))]

/-- The iterates of an initial point with `|Im z|₁ < (1 - Γ(b - a)) ℓ'` stay in the open
sub-strip `S_{ℓ'}`. -/
theorem pic_mem_strip (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ strip ((1 - Γ * (b - a)) * ℓ')) {s : ℝ} (hs : s ∈ Icc a b) (n : ℕ) :
    ∀ τ ∈ Icc a b, pic v ℓ' n τ z s ∈ strip ℓ' := by
  have hℓ : 0 < ℓ := hw.hℓ'.trans hw.hℓℓ
  have hz0 : z ∈ Z0 ℓ' Γ a b := strip_subset_cstrip _ hz
  intro τ hτ
  cases n with
  | zero =>
    show imL1 z < ℓ'
    have : imL1 z < (1 - Γ * (b - a)) * ℓ' := hz
    have hΓT0 : 0 ≤ Γ * (b - a) := mul_nonneg hv.hΓ (sub_nonneg.mpr hw.hab)
    nlinarith [hw.hℓ']
  | succ n =>
    show imL1 (pic v ℓ' (n + 1) τ z s) < ℓ'
    rw [pic_succ]
    have hint := imL1_integral_le (intervalIntegrable_rf_pic hv hw n z s s τ)
    have hbd : ∫ σ in Ι s τ, imL1 (rf v ℓ' σ (pic v ℓ' n σ z s)) ≤ (Γ * ℓ') * |τ - s| := by
      refine setIntegral_uIoc_le_const (fun σ hσ => ?_) (fun σ _ => imL1_nonneg _)
      have hm := pic_mem hv hw hz0 hs n σ (uIoc_subset_window hτ hs hσ)
      rw [rf_eq hw.hℓ' hm]
      exact (hv.imL1_le hℓ σ (cstrip_subset_strip hw.hℓℓ hm)).trans
        (mul_le_mul_of_nonneg_left hm hv.hΓ)
    have hT := abs_sub_le_window hτ hs
    have h3 : (Γ * ℓ') * |τ - s| ≤ Γ * (b - a) * ℓ' := by
      have := mul_le_mul_of_nonneg_left hT (mul_nonneg hv.hΓ hw.hℓ'.le)
      linarith
    have hz1 : imL1 z < (1 - Γ * (b - a)) * ℓ' := hz
    linarith [imL1_add_le z (∫ σ in s..τ, rf v ℓ' σ (pic v ℓ' n σ z s))]

/-! ### Geometric convergence -/

/-- The constant of the geometric bound. -/
def picC (ℓ' Γ V a b : ℝ) : ℝ := (b - a) * (V + Γ * ℓ')

theorem l1_pic_succ_sub_le (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) (n : ℕ) :
    ∀ τ ∈ Icc a b, l1 (pic v ℓ' (n + 1) τ z s - pic v ℓ' n τ z s) ≤
      picC ℓ' Γ V a b * (Γ * (b - a)) ^ n := by
  have hℓ : 0 < ℓ := hw.hℓ'.trans hw.hℓℓ
  induction n with
  | zero =>
    intro τ hτ
    have e : pic v ℓ' 1 τ z s - pic v ℓ' 0 τ z s = ∫ σ in s..τ, rf v ℓ' σ z := by
      simp only [pic, add_sub_cancel_left]
    rw [e, pow_zero, mul_one]
    refine (l1_integral_le (intervalIntegrable_rf_pic hv hw 0 z s s τ)).trans ?_
    refine (setIntegral_uIoc_le_const (C := V + Γ * ℓ') (fun σ _ => l1_rf_le hv hw σ z)
      (fun σ _ => l1_nonneg _)).trans ?_
    have hT := abs_sub_le_window hτ hs
    have hV0 : 0 ≤ V + Γ * ℓ' := (l1_nonneg _).trans (l1_rf_le hv hw a z)
    unfold picC
    nlinarith
  | succ n ih =>
    intro τ hτ
    have e : pic v ℓ' (n + 2) τ z s - pic v ℓ' (n + 1) τ z s =
        ∫ σ in s..τ, (rf v ℓ' σ (pic v ℓ' (n + 1) σ z s) - rf v ℓ' σ (pic v ℓ' n σ z s)) := by
      rw [pic_succ, pic_succ (n := n), add_sub_add_left_eq_sub,
        intervalIntegral.integral_sub (intervalIntegrable_rf_pic hv hw _ z s s τ)
          (intervalIntegrable_rf_pic hv hw _ z s s τ)]
    rw [e]
    refine (l1_integral_le ((intervalIntegrable_rf_pic hv hw _ z s s τ).sub
      (intervalIntegrable_rf_pic hv hw _ z s s τ))).trans ?_
    have hbd : ∫ σ in Ι s τ, l1 (rf v ℓ' σ (pic v ℓ' (n + 1) σ z s) -
        rf v ℓ' σ (pic v ℓ' n σ z s)) ≤
        (Γ * (picC ℓ' Γ V a b * (Γ * (b - a)) ^ n)) * |τ - s| := by
      refine setIntegral_uIoc_le_const (fun σ hσ => ?_) (fun σ _ => l1_nonneg _)
      have hσW := uIoc_subset_window hτ hs hσ
      have hm1 := pic_mem hv hw hz hs (n + 1) σ hσW
      have hm0 := pic_mem hv hw hz hs n σ hσW
      rw [rf_eq hw.hℓ' hm1, rf_eq hw.hℓ' hm0]
      exact (hv.lip σ _ (cstrip_subset_strip hw.hℓℓ hm1) _ (cstrip_subset_strip hw.hℓℓ hm0)).trans
        (mul_le_mul_of_nonneg_left (ih σ hσW) hv.hΓ)
    refine hbd.trans ?_
    have hT := abs_sub_le_window hτ hs
    have hC0 : 0 ≤ picC ℓ' Γ V a b * (Γ * (b - a)) ^ n :=
      (l1_nonneg _).trans (ih a ⟨le_rfl, hw.hab⟩)
    calc Γ * (picC ℓ' Γ V a b * (Γ * (b - a)) ^ n) * |τ - s|
        ≤ Γ * (picC ℓ' Γ V a b * (Γ * (b - a)) ^ n) * (b - a) :=
          mul_le_mul_of_nonneg_left hT (mul_nonneg hv.hΓ hC0)
      _ = picC ℓ' Γ V a b * (Γ * (b - a)) ^ (n + 1) := by ring

theorem dist_pic_succ_le (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) {τ : ℝ} (hτ : τ ∈ Icc a b) (n : ℕ) :
    dist (pic v ℓ' n τ z s) (pic v ℓ' (n + 1) τ z s) ≤ picC ℓ' Γ V a b * (Γ * (b - a)) ^ n := by
  rw [dist_comm, dist_eq_norm]
  exact (norm_le_l1 _).trans (l1_pic_succ_sub_le hv hw hz hs n τ hτ)

theorem ratio_lt_one (hw : FlowWin ℓ ℓ' Γ a b) : Γ * (b - a) < 1 := by
  linarith [hw.hΓT]

/-! ### The limit -/

/-- **The complex flow**: the limit of the Picard iterates. -/
def cflow (v : ℝ → CVec → CVec) (ℓ' : ℝ) (τ : ℝ) (z : CVec) (s : ℝ) : CVec :=
  limUnder atTop fun n => pic v ℓ' n τ z s

theorem tendsto_pic (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    Tendsto (fun n => pic v ℓ' n τ z s) atTop (𝓝 (cflow v ℓ' τ z s)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric _ _ (ratio_lt_one hw) (dist_pic_succ_le hv hw hz hs hτ)))

theorem dist_pic_cflow_le (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) {τ : ℝ} (hτ : τ ∈ Icc a b) (n : ℕ) :
    dist (pic v ℓ' n τ z s) (cflow v ℓ' τ z s) ≤
      picC ℓ' Γ V a b * (Γ * (b - a)) ^ n / (1 - Γ * (b - a)) :=
  dist_le_of_le_geometric_of_tendsto _ _ (ratio_lt_one hw) (dist_pic_succ_le hv hw hz hs hτ)
    (tendsto_pic hv hw hz hs hτ) n

/-- The domain `[a, b] × Z₀ × [a, b]` of the flow. -/
def flowDom (ℓ' Γ a b : ℝ) : Set (ℝ × CVec × ℝ) := Icc a b ×ˢ (Z0 ℓ' Γ a b ×ˢ Icc a b)

theorem tendstoUniformlyOn_pic (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) :
    TendstoUniformlyOn (fun n (p : ℝ × CVec × ℝ) => pic v ℓ' n p.1 p.2.1 p.2.2)
      (fun p => cflow v ℓ' p.1 p.2.1 p.2.2) atTop (flowDom ℓ' Γ a b) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hr0 : 0 ≤ Γ * (b - a) := mul_nonneg hv.hΓ (sub_nonneg.mpr hw.hab)
  have hr1 := ratio_lt_one hw
  have hlim : Tendsto (fun n : ℕ => picC ℓ' Γ V a b * (Γ * (b - a)) ^ n / (1 - Γ * (b - a)))
      atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (picC ℓ' Γ V a b)
    rw [mul_zero] at this
    simpa using this.div_const (1 - Γ * (b - a))
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  intro p hp
  rw [dist_comm]
  exact (dist_pic_cflow_le hv hw hp.2.1 hp.2.2 hp.1 n).trans_lt hn

theorem continuousOn_cflow (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) :
    ContinuousOn (fun p : ℝ × CVec × ℝ => cflow v ℓ' p.1 p.2.1 p.2.2) (flowDom ℓ' Γ a b) :=
  (tendstoUniformlyOn_pic hv hw).continuousOn
    (Frequently.of_forall fun n => (continuous_pic hv hw n).continuousOn)

theorem cflow_mem (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    cflow v ℓ' τ z s ∈ cstrip ℓ' :=
  (isClosed_cstrip ℓ').mem_of_tendsto (tendsto_pic hv hw hz hs hτ)
    (Eventually.of_forall fun n => pic_mem hv hw hz hs n τ hτ)

theorem continuousOn_cflow_time (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) :
    ContinuousOn (fun σ => cflow v ℓ' σ z s) (Icc a b) := by
  have hc : Continuous fun σ : ℝ => (σ, z, s) := continuous_id.prodMk continuous_const
  have h := (continuousOn_cflow hv hw).comp hc.continuousOn
    (fun σ hσ => (⟨hσ, hz, hs⟩ : (σ, z, s) ∈ flowDom ℓ' Γ a b))
  exact h

/-- **The integral equation of the flow.** -/
theorem cflow_eq (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    cflow v ℓ' τ z s = z + ∫ σ in s..τ, v σ (cflow v ℓ' σ z s) := by
  have hsub : uIcc s τ ⊆ Icc a b := uIcc_subset_Icc hs hτ
  have hcont : ContinuousOn (fun σ => v σ (cflow v ℓ' σ z s)) (uIcc s τ) := by
    refine hv.cont.comp ((continuous_id.continuousOn).prodMk
      ((continuousOn_cflow_time hv hw hz hs).mono hsub)) fun σ hσ => ⟨mem_univ _, ?_⟩
    exact cstrip_subset_strip hw.hℓℓ (cflow_mem hv hw hz hs (hsub hσ))
  have hint : IntervalIntegrable (fun σ => v σ (cflow v ℓ' σ z s)) volume s τ :=
    hcont.intervalIntegrable
  -- the iterates converge to the right side
  have hlim : Tendsto (fun n => pic v ℓ' (n + 1) τ z s) atTop
      (𝓝 (z + ∫ σ in s..τ, v σ (cflow v ℓ' σ z s))) := by
    refine tendsto_const_nhds.add ?_
    rw [tendsto_iff_dist_tendsto_zero]
    have hr0 : 0 ≤ Γ * (b - a) := mul_nonneg hv.hΓ (sub_nonneg.mpr hw.hab)
    have hr1 := ratio_lt_one hw
    have hbound : ∀ n, dist (∫ σ in s..τ, rf v ℓ' σ (pic v ℓ' n σ z s))
        (∫ σ in s..τ, v σ (cflow v ℓ' σ z s)) ≤
        2 * ((Γ * (picC ℓ' Γ V a b * (Γ * (b - a)) ^ n / (1 - Γ * (b - a)))) * |τ - s|) := by
      intro n
      rw [dist_eq_norm, ← intervalIntegral.integral_sub (intervalIntegrable_rf_pic hv hw n z s s τ)
        hint]
      refine (norm_le_l1 _).trans ((l1_integral_le ((intervalIntegrable_rf_pic hv hw n z s s τ).sub
        hint)).trans ?_)
      have h := setIntegral_uIoc_le_const (a := s) (b := τ)
        (g := fun σ => l1 (rf v ℓ' σ (pic v ℓ' n σ z s) - v σ (cflow v ℓ' σ z s)))
        (C := Γ * (2 * (picC ℓ' Γ V a b * (Γ * (b - a)) ^ n / (1 - Γ * (b - a)))))
        (fun σ hσ => ?_) (fun σ _ => l1_nonneg _)
      · refine h.trans (le_of_eq ?_)
        ring
      · have hσW := uIoc_subset_window hτ hs hσ
        have hm := pic_mem hv hw hz hs n σ hσW
        have hc := cflow_mem hv hw hz hs hσW
        rw [rf_eq hw.hℓ' hm]
        refine (hv.lip σ _ (cstrip_subset_strip hw.hℓℓ hm) _ (cstrip_subset_strip hw.hℓℓ hc)).trans
          (mul_le_mul_of_nonneg_left ?_ hv.hΓ)
        refine (l1_le_two_mul_norm _).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
        rw [← dist_eq_norm]
        exact dist_pic_cflow_le hv hw hz hs hσW n
    have hzero : Tendsto (fun n : ℕ =>
        2 * ((Γ * (picC ℓ' Γ V a b * (Γ * (b - a)) ^ n / (1 - Γ * (b - a)))) * |τ - s|))
        atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
        (2 * (Γ * picC ℓ' Γ V a b / (1 - Γ * (b - a)) * |τ - s|))
      rw [mul_zero] at this
      refine this.congr fun n => ?_
      ring
    exact squeeze_zero (fun n => dist_nonneg) hbound hzero
  have h1 := (tendsto_pic hv hw hz hs hτ).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique h1 hlim

theorem cflow_start (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) : cflow v ℓ' s z s = z := by
  rw [cflow_eq hv hw hz hs hs, intervalIntegral.integral_same, add_zero]

/-! ### Reality -/

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Metric Set Filter Complex
open scoped Topology Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **Holomorphy of parametric interval integrals.** If `g(x, u)` is holomorphic in `x ∈ U`
(an open subset of a finite-dimensional complex space) for every `u` of a compact interval and
jointly continuous, then `x ↦ ∫_a^b g(x, u) du` is holomorphic on `U`
(`differentiableOn_intervalIntegral_of_param`). The derivative is dominated by Cauchy's estimate
on a ball (`GenSem.norm_fderiv_le_of_closedBall`); it is continuous in `u`, hence measurable,
because each directional derivative is a Cauchy integral of a jointly continuous function
(`continuousOn_fderiv_param`). -/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]

omit [FiniteDimensional ℂ X] in
/-- The directional derivative as a Cauchy integral along a line. -/
theorem fderiv_apply_eq_cauchy {F : X → ℂ} {U : Set X} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {y v : X} {r : ℝ} (hr : 0 < r)
    (hyU : ∀ ζ : ℂ, ‖ζ‖ ≤ r → y + ζ • v ∈ U) :
    fderiv ℂ F y v = (2 * Real.pi * I)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * Real.pi, GenSem.cauchyKernel r θ • F (y + circleMap 0 r θ • v) := by
  have hy : y ∈ U := by simpa using hyU 0 (by simp [hr.le])
  have hdiffy : DifferentiableAt ℂ F y := (hF y hy).differentiableAt (hU.mem_nhds hy)
  have hψ : DifferentiableOn ℂ (fun ζ : ℂ => F (y + ζ • v)) (closedBall (0 : ℂ) r) := by
    refine DifferentiableOn.comp (f := fun ζ : ℂ => y + ζ • v) hF ?_
      (fun ζ hζ => hyU ζ (mem_closedBall_zero_iff.mp hζ))
    exact (differentiable_const _ |>.add (differentiable_id.smul_const v)).differentiableOn
  have hder : deriv (fun ζ : ℂ => F (y + ζ • v)) 0 = fderiv ℂ F y v := by
    have h1 : HasDerivAt (fun ζ : ℂ => y + ζ • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    have h2 : HasFDerivAt F (fderiv ℂ F y) (y + (0 : ℂ) • v) := by
      simpa using hdiffy.hasFDerivAt
    exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv
  have hc := hψ.deriv_eq_smul_circleIntegral hr
  have hint : (∮ z in C(0, r), (1 / (z - 0) ^ 2) • F (y + z • v)) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, GenSem.cauchyKernel r θ • F (y + circleMap 0 r θ • v) := by
    unfold circleIntegral
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only
    rw [← smul_assoc, GenSem.cauchyKernel_eq hr]
  rw [hint, hder] at hc
  have h2pi : (2 * Real.pi * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [hc, smul_smul, inv_mul_cancel₀ h2pi, one_smul]

/-- **The derivative in the parameter is continuous in `u`.** -/
theorem continuousOn_fderiv_param {U : Set X} (hU : IsOpen U) {g : X → ℝ → ℂ} {S : Set ℝ}
    (hS : IsCompact S) (hd : ∀ u ∈ S, DifferentiableOn ℂ (fun x => g x u) U)
    (hc : ContinuousOn (fun q : X × ℝ => g q.1 q.2) (U ×ˢ S)) {x₀ : X} (hx₀ : x₀ ∈ U) :
    ContinuousOn (fun u => fderiv ℂ (fun x => g x u) x₀) S := by
  refine (continuousOn_clm_apply).mpr fun v => ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  set r : ℝ := ε / 2 / (‖v‖ + 1) with hr_def
  have hr : 0 < r := by positivity
  have hmem : ∀ ζ : ℂ, ‖ζ‖ ≤ r → x₀ + ζ • v ∈ U := by
    intro ζ hζ
    apply hεU
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have h1 : ‖ζ‖ * ‖v‖ ≤ r * ‖v‖ := mul_le_mul_of_nonneg_right hζ (norm_nonneg v)
    have h2 : r * ‖v‖ < ε := by
      rw [hr_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]
    linarith
  -- the Cauchy integral representation on `S`
  have hrep : ∀ u ∈ S, fderiv ℂ (fun x => g x u) x₀ v = (2 * Real.pi * I)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * Real.pi, GenSem.cauchyKernel r θ • g (x₀ + circleMap 0 r θ • v) u :=
    fun u hu => fderiv_apply_eq_cauchy hU (hd u hu) hr hmem
  refine ContinuousOn.congr ?_ hrep
  refine ContinuousOn.const_smul ?_ ((2 * Real.pi * I)⁻¹)
  -- continuity of the parametric integral, through a continuous extension
  have hnorm : ∀ θ : ℝ, ‖circleMap 0 r θ‖ ≤ r := fun θ => by simp [abs_of_pos hr]
  have hK : ∀ u ∈ S, Continuous fun θ : ℝ =>
      GenSem.cauchyKernel r θ • g (x₀ + circleMap 0 r θ • v) u := by
    intro u hu
    refine (GenSem.continuous_cauchyKernel hr).smul ?_
    exact hc.comp_continuous ((continuous_const.add ((continuous_circleMap 0 r).smul
      continuous_const)).prodMk continuous_const) fun θ => ⟨hmem _ (hnorm θ), hu⟩
  intro u₀ hu₀
  have hjoint : ContinuousOn (fun p : ℝ × ℝ =>
      GenSem.cauchyKernel r p.2 • g (x₀ + circleMap 0 r p.2 • v) p.1) (S ×ˢ univ) := by
    refine ((GenSem.continuous_cauchyKernel hr).comp continuous_snd).continuousOn.smul ?_
    refine hc.comp ((continuous_const.add (((continuous_circleMap 0 r).comp continuous_snd).smul
      continuous_const)).prodMk continuous_fst).continuousOn fun p hp => ⟨hmem _ (hnorm _), hp.1⟩
  -- dominated convergence on the compact parameter set
  have hcomp : IsCompact (S ×ˢ Icc (0 : ℝ) (2 * Real.pi)) := hS.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn (hjoint.mono
    (prod_mono subset_rfl (subset_univ _)))
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := fun _ => M) ?_ ?_ intervalIntegrable_const ?_
  · exact eventually_nhdsWithin_of_forall fun u hu => (hK u hu).aestronglyMeasurable
  · refine eventually_nhdsWithin_of_forall fun u hu => Eventually.of_forall fun θ hθ => ?_
    have hθ' : θ ∈ Icc (0 : ℝ) (2 * Real.pi) := by
      rw [uIoc_of_le (by positivity)] at hθ; exact ⟨hθ.1.le, hθ.2⟩
    exact hM (u, θ) ⟨hu, hθ'⟩
  · refine Eventually.of_forall fun θ _ => ?_
    exact (hjoint.comp (continuous_id.prodMk continuous_const).continuousOn
      fun u hu => ⟨hu, mem_univ _⟩) u₀ hu₀

/-- **Holomorphy of a parametric interval integral.** -/
theorem differentiableOn_intervalIntegral_of_param {U : Set X} (hU : IsOpen U) {g : X → ℝ → ℂ}
    {a b : ℝ} (hd : ∀ u ∈ uIcc a b, DifferentiableOn ℂ (fun x => g x u) U)
    (hc : ContinuousOn (fun q : X × ℝ => g q.1 q.2) (U ×ˢ uIcc a b)) :
    DifferentiableOn ℂ (fun x => ∫ u in a..b, g x u) U := by
  have : ProperSpace X := FiniteDimensional.proper ℂ X
  intro x₀ hx₀
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  set ρ : ℝ := ε / 4 with hρ_def
  have hρ : 0 < ρ := by positivity
  have hcb : closedBall x₀ (3 * ρ) ⊆ U := fun x hx => hεU (by
    rw [mem_ball]; rw [mem_closedBall] at hx; linarith)
  have hcomp : IsCompact (closedBall x₀ (3 * ρ) ×ˢ uIcc a b) :=
    (isCompact_closedBall x₀ _).prod isCompact_uIcc
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn (hc.mono (prod_mono hcb subset_rfl))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (x₀, a) ⟨mem_closedBall_self (by positivity),
    left_mem_uIcc⟩)
  have hball : ball x₀ ρ ⊆ U := (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith))).trans hcb
  -- Cauchy's estimate for the derivative on the ball
  have hbd : ∀ u ∈ uIcc a b, ∀ x ∈ ball x₀ ρ, ‖fderiv ℂ (fun x => g x u) x‖ ≤ M / ρ := by
    intro u hu x hx
    have hsub : closedBall x ρ ⊆ closedBall x₀ (3 * ρ) := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      rw [mem_ball] at hx
      have := dist_triangle w x x₀
      linarith
    exact GenSem.norm_fderiv_le_of_closedBall hρ ((hd u hu).mono (hsub.trans hcb))
      fun w hw => hM (w, u) ⟨hsub hw, hu⟩
  have hgc : ∀ x ∈ U, ContinuousOn (fun u => g x u) (uIcc a b) := fun x hx =>
    hc.comp (continuous_const.prodMk continuous_id).continuousOn fun u hu => ⟨hx, hu⟩
  have hF' := continuousOn_fderiv_param hU isCompact_uIcc hd hc hx₀
  have hB : HasFDerivAt (fun x => ∫ u in a..b, g x u)
      (∫ u in a..b, fderiv ℂ (fun x => g x u) x₀) x₀ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
      (μ := volume) (F := g) (F' := fun x u => fderiv ℂ (fun x => g x u) x)
      (bound := fun _ => M / ρ) (s := ball x₀ ρ) (ball_mem_nhds x₀ hρ) ?_ ?_ ?_ ?_ ?_ ?_
    · exact eventually_of_mem (ball_mem_nhds x₀ hρ) fun x hx =>
        ((hgc x (hball hx)).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · exact (hgc x₀ hx₀).intervalIntegrable
    · exact (hF'.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · refine Eventually.of_forall fun u hu x hx => hbd u (uIoc_subset_uIcc hu) x hx
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun u hu x hx => ?_
      exact ((hd u (uIoc_subset_uIcc hu)) x (hball hx)).differentiableAt
        (hU.mem_nhds (hball hx)) |>.hasFDerivAt
  exact hB.differentiableAt.differentiableWithinAt

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Homogenization
open scoped Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **Uniqueness, the imaginary part, and real trajectories.**
* `eq_cflow_of_integral`: a continuous curve in `S_ℓ` solving the integral equation of the flow on
  the window is the flow (the difference is bounded by `Γ(b-a) < 1` times its own supremum).
* `imL1_cflow_le`: `|Im X(τ, z, s)|₁ ≤ |Im z|₁ / (1 - Γ(b - a))`.
* `cflow_ofRealVec_eq`: at real initial points the complex flow is the real flow `X` of a real
  field `u` whose complexification `v` restricts to `u` on real points (the complex flow extends
  the real flow, as in Lemma 6.6 of the paper). -/

section
variable {v : ℝ → CVec → CVec} {ℓ ℓ' Γ V a b : ℝ}

/-- The real points as a continuous `ℝ`-linear map. -/
def ofRealVecCLM : Vec 2 →L[ℝ] CVec :=
  ContinuousLinearMap.pi fun c => Complex.ofRealCLM.comp (ContinuousLinearMap.proj c)

theorem ofRealVecCLM_apply (x : Vec 2) : ofRealVecCLM x = ofRealVec x := rfl

/-- **Uniqueness**: a continuous curve in `S_ℓ` solving the integral equation is the flow. -/
theorem eq_cflow_of_integral (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) {γ : ℝ → CVec}
    (hγc : ContinuousOn γ (Icc a b)) (hγs : ∀ σ ∈ Icc a b, γ σ ∈ strip ℓ)
    (hγ : ∀ τ ∈ Icc a b, γ τ = z + ∫ σ in s..τ, v σ (γ σ)) :
    ∀ τ ∈ Icc a b, γ τ = cflow v ℓ' τ z s := by
  have hcf := continuousOn_cflow_time hv hw hz hs
  have hD : ContinuousOn (fun σ => l1 (γ σ - cflow v ℓ' σ z s)) (Icc a b) :=
    continuous_l1.comp_continuousOn (hγc.sub hcf)
  obtain ⟨σ₀, hσ₀, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, le_rfl, hw.hab⟩ hD
  set M := l1 (γ σ₀ - cflow v ℓ' σ₀ z s) with hM
  have hint : ∀ τ ∈ Icc a b, ∀ g : ℝ → CVec, ContinuousOn g (Icc a b) →
      (∀ σ ∈ Icc a b, g σ ∈ strip ℓ) → IntervalIntegrable (fun σ => v σ (g σ)) volume s τ := by
    intro τ hτ g hg hgs
    refine ContinuousOn.intervalIntegrable ?_
    refine hv.cont.comp (continuous_id.continuousOn.prodMk (hg.mono (uIcc_subset_Icc hs hτ)))
      fun σ hσ => ⟨mem_univ _, hgs σ (uIcc_subset_Icc hs hτ hσ)⟩
  have hcs : ∀ σ ∈ Icc a b, cflow v ℓ' σ z s ∈ strip ℓ :=
    fun σ hσ => cstrip_subset_strip hw.hℓℓ (cflow_mem hv hw hz hs hσ)
  have hbound : ∀ τ ∈ Icc a b, l1 (γ τ - cflow v ℓ' τ z s) ≤ Γ * (b - a) * M := by
    intro τ hτ
    rw [hγ τ hτ, cflow_eq hv hw hz hs hτ, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (hint τ hτ γ hγc hγs) (hint τ hτ _ hcf hcs)]
    refine (l1_integral_le ((hint τ hτ γ hγc hγs).sub (hint τ hτ _ hcf hcs))).trans ?_
    refine (setIntegral_uIoc_le_const (C := Γ * M) (fun σ hσ => ?_)
      (fun σ _ => l1_nonneg _)).trans ?_
    · have hσW := uIoc_subset_window hτ hs hσ
      exact (hv.lip σ _ (hγs σ hσW) _ (hcs σ hσW)).trans
        (mul_le_mul_of_nonneg_left (hmax hσW) hv.hΓ)
    · have hM0 : 0 ≤ M := l1_nonneg _
      have := abs_sub_le_window hτ hs
      have h1 : Γ * M * |τ - s| ≤ Γ * M * (b - a) :=
        mul_le_mul_of_nonneg_left this (mul_nonneg hv.hΓ hM0)
      linarith
  have hM0 : M ≤ 0 := by
    have h1 := hbound σ₀ hσ₀
    have hr := ratio_lt_one hw
    have hM0 : 0 ≤ M := l1_nonneg _
    nlinarith
  intro τ hτ
  have h0 : l1 (γ τ - cflow v ℓ' τ z s) = 0 :=
    le_antisymm ((hmax hτ).trans hM0) (l1_nonneg _)
  have h1 : ‖γ τ - cflow v ℓ' τ z s‖ = 0 :=
    le_antisymm ((norm_le_l1 _).trans h0.le) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp h1)

/-- **The imaginary part along the flow**: `|Im X(τ)|₁ ≤ |Im z|₁ / (1 - Γ(b - a))`. -/
theorem imL1_pic_le (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) (n : ℕ) :
    ∀ τ ∈ Icc a b, imL1 (pic v ℓ' n τ z s) ≤ imL1 z / (1 - Γ * (b - a)) := by
  have hℓ : 0 < ℓ := hw.hℓ'.trans hw.hℓℓ
  have hr := ratio_lt_one hw
  have hr0 : 0 ≤ Γ * (b - a) := mul_nonneg hv.hΓ (sub_nonneg.mpr hw.hab)
  have h1r : 0 < 1 - Γ * (b - a) := by linarith
  have hz0 := imL1_nonneg z
  have hle : imL1 z ≤ imL1 z / (1 - Γ * (b - a)) := by
    rw [le_div_iff₀ h1r]
    nlinarith
  induction n with
  | zero => exact fun _ _ => hle
  | succ n ih =>
    intro τ hτ
    rw [pic_succ]
    refine (imL1_add_le _ _).trans ?_
    refine (add_le_add le_rfl (imL1_integral_le (intervalIntegrable_rf_pic hv hw n z s s τ))).trans ?_
    have hbd : ∫ σ in Ι s τ, imL1 (rf v ℓ' σ (pic v ℓ' n σ z s)) ≤
        (Γ * (imL1 z / (1 - Γ * (b - a)))) * |τ - s| := by
      refine setIntegral_uIoc_le_const (fun σ hσ => ?_) (fun σ _ => imL1_nonneg _)
      have hσW := uIoc_subset_window hτ hs hσ
      have hm := pic_mem hv hw hz hs n σ hσW
      rw [rf_eq hw.hℓ' hm]
      exact (hv.imL1_le hℓ σ (cstrip_subset_strip hw.hℓℓ hm)).trans
        (mul_le_mul_of_nonneg_left (ih σ hσW) hv.hΓ)
    have hT := abs_sub_le_window hτ hs
    have hq0 : 0 ≤ imL1 z / (1 - Γ * (b - a)) := div_nonneg hz0 h1r.le
    have h2 : (Γ * (imL1 z / (1 - Γ * (b - a)))) * |τ - s| ≤
        Γ * (b - a) * (imL1 z / (1 - Γ * (b - a))) := by
      have := mul_le_mul_of_nonneg_left hT (mul_nonneg hv.hΓ hq0)
      linarith
    have h3 : imL1 z + Γ * (b - a) * (imL1 z / (1 - Γ * (b - a))) =
        imL1 z / (1 - Γ * (b - a)) := by
      field_simp
      ring
    linarith

theorem imL1_cflow_le (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    imL1 (cflow v ℓ' τ z s) ≤ imL1 z / (1 - Γ * (b - a)) :=
  le_of_tendsto ((continuous_imL1.tendsto _).comp (tendsto_pic hv hw hz hs hτ))
    (Eventually.of_forall fun n => imL1_pic_le hv hw hz hs n τ hτ)

/-- **At real initial points the complex flow is the real flow** of the real field `u` whose
complexification is `v` on real points. -/
theorem cflow_ofRealVec_eq (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b)
    {u : ℝ → Vec 2 → Vec 2} (hu : Continuous fun p : ℝ × Vec 2 => u p.1 p.2)
    (huv : ∀ t y, v t (ofRealVec y) = ofRealVec (u t y)) {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow u X) (hXc : ∀ x s, Continuous fun σ => X σ x s) (x : Vec 2)
    (hx : ofRealVec x ∈ Z0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) :
    ∀ τ ∈ Icc a b, cflow v ℓ' τ (ofRealVec x) s = ofRealVec (X τ x s) := by
  have hℓ : 0 < ℓ := hw.hℓ'.trans hw.hℓℓ
  intro τ hτ
  refine (eq_cflow_of_integral hv hw hx hs (γ := fun σ => ofRealVec (X σ x s))
    ((ofRealVecCLM.continuous.comp (hXc x s)).continuousOn)
    (fun σ _ => ofRealVec_mem_strip hℓ _) (fun τ' hτ' => ?_) τ hτ).symm
  have hcont : Continuous fun σ => ofRealVec (u σ (X σ x s)) :=
    ofRealVecCLM.continuous.comp (hu.comp (continuous_id.prodMk (hXc x s)))
  have hder : ∀ σ ∈ uIcc s τ', HasDerivAt (fun σ => ofRealVec (X σ x s))
      (ofRealVec (u σ (X σ x s))) σ := by
    intro σ _
    have h := ofRealVecCLM.hasFDerivAt.comp_hasDerivAt σ (hX.2 x s σ)
    exact h
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable _ _)
  simp only [huv]
  rw [hftc, hX.1 x s]
  abel
end

/-! **The group law of the complex flow.** For initial points with
`|Im z|₁ ≤ (1 - Γ(b - a))² ℓ'` and times in the window, the flow from the intermediate time `v`
of the point reached at `v` is the flow from `r` (`cflow_group`): the curve `σ ↦ X(σ, z, r)`
solves the integral equation from `v`, and the solution is unique (`eq_cflow_of_integral`). -/

section
variable {v : ℝ → CVec → CVec} {ℓ ℓ' Γ V a b : ℝ}

/-- The points reached from `Z0'` stay in `Z0`. -/
theorem cflow_mem_Z0 (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : imL1 z ≤ (1 - Γ * (b - a)) ^ 2 * ℓ') {s : ℝ} (hs : s ∈ Icc a b) {τ : ℝ}
    (hτ : τ ∈ Icc a b) : cflow v ℓ' τ z s ∈ Z0 ℓ' Γ a b := by
  have hr := ratio_lt_one hw
  have hr0 : 0 ≤ Γ * (b - a) := mul_nonneg hv.hΓ (sub_nonneg.mpr hw.hab)
  have h1r : 0 < 1 - Γ * (b - a) := by linarith
  have hz0 : z ∈ Z0 ℓ' Γ a b := by
    show imL1 z ≤ (1 - Γ * (b - a)) * ℓ'
    refine hz.trans ?_
    have : (1 - Γ * (b - a)) ^ 2 ≤ 1 - Γ * (b - a) := by nlinarith
    exact mul_le_mul_of_nonneg_right this hw.hℓ'.le
  have h := imL1_cflow_le hv hw hz0 hs hτ
  show imL1 (cflow v ℓ' τ z s) ≤ (1 - Γ * (b - a)) * ℓ'
  refine h.trans ?_
  rw [div_le_iff₀ h1r]
  calc imL1 z ≤ (1 - Γ * (b - a)) ^ 2 * ℓ' := hz
    _ = (1 - Γ * (b - a)) * ℓ' * (1 - Γ * (b - a)) := by ring

/-- **The group law of the complex flow.** -/
theorem cflow_group (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : imL1 z ≤ (1 - Γ * (b - a)) ^ 2 * ℓ') {r : ℝ} (hr : r ∈ Icc a b) {w : ℝ}
    (hw' : w ∈ Icc a b) {u : ℝ} (hu : u ∈ Icc a b) :
    cflow v ℓ' u (cflow v ℓ' w z r) w = cflow v ℓ' u z r := by
  have hr1 := ratio_lt_one hw
  have hr0 : 0 ≤ Γ * (b - a) := mul_nonneg hv.hΓ (sub_nonneg.mpr hw.hab)
  have hz0 : z ∈ Z0 ℓ' Γ a b := by
    show imL1 z ≤ (1 - Γ * (b - a)) * ℓ'
    refine hz.trans ?_
    have : (1 - Γ * (b - a)) ^ 2 ≤ 1 - Γ * (b - a) := by nlinarith
    exact mul_le_mul_of_nonneg_right this hw.hℓ'.le
  have hzw := cflow_mem_Z0 hv hw hz hr hw'
  have hcont := continuousOn_cflow_time hv hw hz0 hr
  have hstrip : ∀ σ ∈ Icc a b, cflow v ℓ' σ z r ∈ strip ℓ :=
    fun σ hσ => cstrip_subset_strip hw.hℓℓ (cflow_mem hv hw hz0 hr hσ)
  have hint : ∀ τ ∈ Icc a b, IntervalIntegrable (fun σ => v σ (cflow v ℓ' σ z r)) volume r τ := by
    intro τ hτ
    refine ContinuousOn.intervalIntegrable ?_
    exact hv.cont.comp (continuous_id.continuousOn.prodMk (hcont.mono (uIcc_subset_Icc hr hτ)))
      fun σ hσ => ⟨mem_univ _, hstrip σ (uIcc_subset_Icc hr hτ hσ)⟩
  refine (eq_cflow_of_integral hv hw hzw hw' hcont hstrip (fun τ hτ => ?_) u hu).symm
  -- the curve solves the integral equation from `w`
  rw [cflow_eq hv hw hz0 hr hτ, cflow_eq hv hw hz0 hr hw', add_assoc,
    intervalIntegral.integral_add_adjacent_intervals (hint w hw') ?_]
  exact (hint w hw').symm.trans (hint τ hτ)
end

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Metric Set Complex Filter Topology
open scoped Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **Derivatives of holomorphic functions with a real parameter.** If `F(t, z)` is
jointly continuous on `ℝ × U` and holomorphic in `z` on the open set `U`, then its complex
derivative is jointly continuous on `ℝ × U`. The
proof writes the directional derivative by the Cauchy formula on a small circle in the direction
(`fderiv_apply_eq_circle`) and takes the parametric integral
(`continuousAt_fderiv_apply_of_param`). -/

open AVRegularity.Providers.GenSem

/-- **The Cauchy formula for a directional derivative** on a circle of radius `r` in the
direction `w`. -/
theorem fderiv_apply_eq_circle {U : Set CVec} (hU : IsOpen U) {F : CVec → ℂ}
    (hF : DifferentiableOn ℂ F U) {y w : CVec} {r : ℝ} (hr : 0 < r)
    (hyU : ∀ ζ : ℂ, ‖ζ‖ ≤ r → y + ζ • w ∈ U) :
    fderiv ℂ F y w = (2 * Real.pi * I)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * Real.pi, cauchyKernel r θ • F (y + circleMap 0 r θ • w) := by
  have hy : y ∈ U := by simpa using hyU 0 (by simp [hr.le])
  have hdiffy : DifferentiableAt ℂ F y := (hF y hy).differentiableAt (hU.mem_nhds hy)
  have hψ : DifferentiableOn ℂ (fun ζ : ℂ => F (y + ζ • w)) (closedBall (0 : ℂ) r) := by
    refine DifferentiableOn.comp (f := fun ζ : ℂ => y + ζ • w) hF ?_
      (fun ζ hζ => hyU ζ (mem_closedBall_zero_iff.mp hζ))
    exact (differentiable_const _ |>.add (differentiable_id.smul_const w)).differentiableOn
  have hder : deriv (fun ζ : ℂ => F (y + ζ • w)) 0 = fderiv ℂ F y w := by
    have h1 : HasDerivAt (fun ζ : ℂ => y + ζ • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const w).const_add y
    have h2 : HasFDerivAt F (fderiv ℂ F y) (y + (0 : ℂ) • w) := by
      simpa using hdiffy.hasFDerivAt
    exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv
  have hc := hψ.deriv_eq_smul_circleIntegral hr
  have hint : (∮ z in C(0, r), (1 / (z - 0) ^ 2) • F (y + z • w)) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, cauchyKernel r θ • F (y + circleMap 0 r θ • w) := by
    unfold circleIntegral
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only
    rw [← smul_assoc, cauchyKernel_eq hr]
  rw [hint, hder] at hc
  have h2pi : (2 * Real.pi * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [hc, smul_smul, inv_mul_cancel₀ h2pi, one_smul]

/-- **The directional derivative of a holomorphic function with a real parameter is jointly
continuous.** -/
theorem continuousAt_fderiv_apply_of_param {U : Set CVec} (hU : IsOpen U) {F : ℝ → CVec → ℂ}
    (hc : ContinuousOn (fun p : ℝ × CVec => F p.1 p.2) (univ ×ˢ U))
    (hd : ∀ t, DifferentiableOn ℂ (F t) U) (w : CVec) {p₀ : ℝ × CVec} (hp₀ : p₀.2 ∈ U) :
    ContinuousAt (fun p : ℝ × CVec => fderiv ℂ (F p.1) p.2 w) p₀ := by
  obtain ⟨t₀, y₀⟩ := p₀
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU y₀ hp₀
  set ρ : ℝ := ε / 4 with hρ_def
  have hρ : 0 < ρ := by positivity
  set r : ℝ := ρ / (‖w‖ + 1) with hr_def
  have hr : 0 < r := by positivity
  have hrv : r * ‖w‖ ≤ ρ := by
    rw [hr_def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg w, hρ]
  have hball : closedBall y₀ (2 * ρ) ⊆ U := fun z hz =>
    hεU (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  have hmem : ∀ y ∈ ball y₀ ρ, ∀ ζ : ℂ, ‖ζ‖ ≤ r → y + ζ • w ∈ closedBall y₀ (2 * ρ) := by
    intro y hy ζ hζ
    rw [mem_ball, dist_eq_norm] at hy
    rw [mem_closedBall, dist_eq_norm]
    have h1 : ‖ζ • w‖ ≤ ρ := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right hζ (norm_nonneg w)).trans hrv
    calc ‖y + ζ • w - y₀‖ = ‖(y - y₀) + ζ • w‖ := by congr 1; abel
      _ ≤ ‖y - y₀‖ + ‖ζ • w‖ := norm_add_le _ _
      _ ≤ 2 * ρ := by linarith
  have hnorm_e : ∀ θ : ℝ, ‖circleMap 0 r θ‖ ≤ r := fun θ => by
    simp [abs_of_pos hr]
  -- a bound of `F` on a compact neighbourhood
  have hK : IsCompact (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (2 * ρ)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hc.mono (prod_mono (subset_univ _) hball))
  let H : ℝ × CVec → ℝ → ℂ := fun p θ => cauchyKernel r θ • F p.1 (p.2 + circleMap 0 r θ • w)
  have hnhds : ∀ᶠ p : ℝ × CVec in 𝓝 (t₀, y₀), p.1 ∈ Ioo (t₀ - 1) (t₀ + 1) ∧ p.2 ∈ ball y₀ ρ :=
    prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) (ball_mem_nhds y₀ hρ)
  have hHcont : ∀ p : ℝ × CVec, p.2 ∈ ball y₀ ρ → Continuous (H p) := by
    intro p hp
    refine (continuous_cauchyKernel hr).smul ?_
    exact (hd p.1).continuousOn.comp_continuous
      (continuous_const.add ((continuous_circleMap 0 r).smul continuous_const))
      fun θ => hball (hmem p.2 hp _ (hnorm_e θ))
  -- the integral is continuous at `(t₀, y₀)`
  have hI : ContinuousAt (fun p : ℝ × CVec => ∫ θ in (0 : ℝ)..2 * Real.pi, H p θ) (t₀, y₀) := by
    refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => 1 / r * M) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [hnhds] with p hp
      exact (hHcont p hp.2).aestronglyMeasurable
    · filter_upwards [hnhds] with p hp
      refine Eventually.of_forall fun θ _ => ?_
      show ‖cauchyKernel r θ • F p.1 (p.2 + circleMap 0 r θ • w)‖ ≤ 1 / r * M
      rw [norm_smul, cauchyKernel_norm hr]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact hM (p.1, p.2 + circleMap 0 r θ • w)
        ⟨Ioo_subset_Icc_self hp.1, hmem p.2 hp.2 _ (hnorm_e θ)⟩
    · refine Eventually.of_forall fun θ _ => ?_
      have hpt : (t₀, y₀ + circleMap 0 r θ • w) ∈ univ ×ˢ U :=
        ⟨mem_univ _, hball (hmem y₀ (mem_ball_self hρ) _ (hnorm_e θ))⟩
      have hFc : ContinuousAt (fun p : ℝ × CVec => F p.1 p.2) (t₀, y₀ + circleMap 0 r θ • w) :=
        hc.continuousAt (prod_mem_nhds univ_mem (hU.mem_nhds hpt.2))
      have hg : Continuous fun p : ℝ × CVec => (p.1, p.2 + circleMap 0 r θ • w) :=
        continuous_fst.prodMk (continuous_snd.add continuous_const)
      have h3 : ContinuousAt (fun p : ℝ × CVec => F p.1 (p.2 + circleMap 0 r θ • w)) (t₀, y₀) :=
        ContinuousAt.comp (g := fun p : ℝ × CVec => F p.1 p.2)
          (f := fun p : ℝ × CVec => (p.1, p.2 + circleMap 0 r θ • w)) hFc hg.continuousAt
      exact h3.const_smul (cauchyKernel r θ)
  -- the derivative is the integral near `(t₀, y₀)`
  have heq : (fun p : ℝ × CVec => fderiv ℂ (F p.1) p.2 w) =ᶠ[𝓝 (t₀, y₀)]
      fun p => (2 * Real.pi * I)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, H p θ := by
    filter_upwards [hnhds] with p hp
    exact fderiv_apply_eq_circle hU (hd p.1) hr fun ζ hζ => hball (hmem p.2 hp.2 ζ hζ)
  exact (hI.const_smul ((2 * Real.pi * I)⁻¹)).congr heq.symm

end AVRegularity.Providers.ComplexFlow
end
