-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.TorusDist
public import AVenhance.Statements.Roots.UnitCube
public import AVenhance.Statements.Roots.IsZ2Periodic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import AVRegularity.Applications.Dissipation.TorusShift
import AVRegularity.Applications.Dissipation.Rows
import Mathlib.MeasureTheory.Integral.Prod

/-! # The operator lemma: positive Hölder-smoothing operators contract mean-zero functions

Let `P : L²(𝕋²) → C(𝕋²)` be linear, positive,
with `P1 = 1`, `∫ P f = ∫ f`, `‖P f‖_∞ ≤ C ‖f‖₂` and `|P f(x) - P f(y)| ≤ C d(x,y)^s ‖f‖₂`,
`C ≥ 1`, `s > 0`. Then `‖P f‖₂² ≤ (1 - 1/(2N⁴)) ‖f‖₂²` for mean-zero `f`, `N = ⌈C^{1/s}⌉`.
Lemma 8.4 of the paper follows from it.

Carriers: `L²(𝕋²)` is `Lp ℝ 2 (volume.restrict unitCube)`; `C(𝕋²)` is continuous functions on
`Vec 2` (periodicity of `P f` follows from the Hölder bound, since `d(x, x + n) = 0`); `d` is
`torusDist`. The proof is that of Lemma 8.4 of the paper: Riesz rows `k_x` with
`P f(x) = ⟪k_x, f⟫`, `k_x ≥ 0`, `∫ k_x dx = 1` in `L²`, the kernel `H(x,y) = ⟪k_x, k_y⟫`, the
adjoint `P*g = ∫ g(x) k_x dx` and the identity (8.18), and the torus inequality
(`integral_sq_le_of_small_translates`, module `Dissipation.TorusShift`). -/

public section

open MeasureTheory Homogenization AVenhance
open scoped InnerProductSpace

namespace AVRegularity.Applications.Dissipation

/-! ### Real arithmetic -/

/-- With `N = ⌈C^{1/s}⌉₊`, `C d^s ≤ 1` for `0 ≤ d ≤ 1/N`. -/
private theorem mul_rpow_le_one_of_le_inv_ceil {s C d : ℝ} (hs : 0 < s) (hC : 1 ≤ C)
    (hd0 : 0 ≤ d) (hd : d ≤ 1 / (⌈C ^ (1 / s)⌉₊ : ℝ)) : C * d ^ s ≤ 1 := by
  have hpos : 0 < C ^ (1 / s) := Real.rpow_pos_of_pos (by linarith) _
  have hN : C ^ (1 / s) ≤ (⌈C ^ (1 / s)⌉₊ : ℝ) := Nat.le_ceil _
  have hNpos : (0 : ℝ) < ⌈C ^ (1 / s)⌉₊ := lt_of_lt_of_le hpos hN
  have h1 : (C ^ (1 / s)) ^ s = C := by
    rw [← Real.rpow_mul (by linarith), one_div_mul_cancel hs.ne', Real.rpow_one]
  have h2 : C ≤ (⌈C ^ (1 / s)⌉₊ : ℝ) ^ s :=
    calc C = (C ^ (1 / s)) ^ s := h1.symm
      _ ≤ (⌈C ^ (1 / s)⌉₊ : ℝ) ^ s := Real.rpow_le_rpow hpos.le hN hs.le
  have h3 : d ^ s ≤ (1 / (⌈C ^ (1 / s)⌉₊ : ℝ)) ^ s := Real.rpow_le_rpow hd0 hd hs.le
  have h4 : (1 / (⌈C ^ (1 / s)⌉₊ : ℝ)) ^ s = 1 / (⌈C ^ (1 / s)⌉₊ : ℝ) ^ s := by
    rw [Real.div_rpow zero_le_one hNpos.le, Real.one_rpow]
  have h5 : 0 < (⌈C ^ (1 / s)⌉₊ : ℝ) ^ s := Real.rpow_pos_of_pos hNpos _
  calc C * d ^ s ≤ (⌈C ^ (1 / s)⌉₊ : ℝ) ^ s * (1 / (⌈C ^ (1 / s)⌉₊ : ℝ) ^ s) :=
        mul_le_mul h2 (h3.trans_eq h4) (Real.rpow_nonneg hd0 _) h5.le
    _ = 1 := mul_one_div_cancel h5.ne'

/-- `1 ≤ ⌈C^{1/s}⌉₊` for `C ≥ 1`. -/
private theorem one_le_ceil_rpow {s C : ℝ} (hC : 1 ≤ C) : 1 ≤ ⌈C ^ (1 / s)⌉₊ :=
  Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1
    (Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by linarith) _)))

/-- Cauchy–Schwarz to contraction: `a ≤ b c` and `b² ≤ θ a` give `a ≤ θ c²`. -/
private theorem le_mul_sq_of_le_mul_of_sq_le {a b c θ : ℝ} (ha : 0 ≤ a) (hθ : 0 ≤ θ)
    (h1 : a ≤ b * c) (h2 : b ^ 2 ≤ θ * a) : a ≤ θ * c ^ 2 := by
  rcases ha.eq_or_lt with h | h
  · rw [← h]
    positivity
  · have h3 : a * a ≤ a * (θ * c ^ 2) :=
      calc a * a ≤ (b * c) * (b * c) := mul_self_le_mul_self ha h1
        _ = b ^ 2 * c ^ 2 := by ring
        _ ≤ (θ * a) * c ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg c)
        _ = a * (θ * c ^ 2) := by ring
    exact le_of_mul_le_mul_left h3 h

/-! ### Boxes -/

private theorem torusDist_nonneg_op (x y : Vec 2) : 0 ≤ torusDist x y :=
  Real.iInf_nonneg fun _ => Real.sqrt_nonneg _

private theorem closedCube_isCompact_op :
    IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
  isCompact_univ_pi fun _ => isCompact_Icc

private theorem box_isCompact (a : ℝ) :
    IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (-a) a) :=
  isCompact_univ_pi fun _ => isCompact_Icc

private theorem box_measurableSet (a : ℝ) :
    MeasurableSet (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (-a) a) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- A continuous function on the product of the cell and a box is integrable. -/
private theorem integrable_unitCube_prod_box {F : Vec 2 × Vec 2 → ℝ} (hF : Continuous F) (a : ℝ) :
    Integrable F ((volume.restrict unitCube).prod
      (volume.restrict (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (-a) a))) := by
  rw [Measure.prod_restrict]
  exact (hF.continuousOn.integrableOn_compact (closedCube_isCompact_op.prod (box_isCompact a)))
    |>.mono_set (Set.prod_mono (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self) subset_rfl)

/-- The cell integral of a periodic function is its integral over the box `x + Q`. -/
private theorem integral_unitCube_eq_centredBox_add {F : Vec 2 → ℝ} (hF : IsZ2Periodic F)
    (x : Vec 2) :
    ∫ y in unitCube, F y =
      ∫ w in Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)), F (x + w) := by
  have hF' : IsZ2Periodic fun w => F (x + w) := fun n w => by
    simp only
    rw [← add_assoc, hF]
  rw [integral_centredBox_eq_unitCube hF', ← integral_unitCube_add_of_isZ2Periodic hF x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [add_comm w x]

/-- Points of `Q/N` are displacements of torus length at most `1/N`. -/
private theorem torusDist_add_le_of_mem_box {N : ℕ} (hN : 1 ≤ N) (x w : Vec 2)
    (hw : w ∈ Set.pi Set.univ
      (fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ))))) :
    torusDist x (x + w) ≤ 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 := hw 0 (Set.mem_univ _)
  have h1 := hw 1 (Set.mem_univ _)
  have hsq : vecNormSq (x - (x + w)) ≤ (1 / (N : ℝ)) ^ 2 := by
    have he : vecNormSq (x - (x + w)) = w 0 ^ 2 + w 1 ^ 2 := by
      simp only [vecNormSq, vecDot, Fin.sum_univ_two, Pi.sub_apply, Pi.add_apply]
      ring
    have hq : (1 / (N : ℝ)) ^ 2 = 4 * (1 / (2 * (N : ℝ))) ^ 2 := by
      field_simp
      ring
    rw [he, hq]
    have := sq_le_sq' h0.1 h0.2
    have := sq_le_sq' h1.1 h1.2
    nlinarith [sq_nonneg (1 / (2 * (N : ℝ)))]
  calc torusDist x (x + w) ≤ √(vecNormSq (x - (x + w))) := torusDist_le_sqrt_vecNormSq _ _
    _ ≤ √((1 / (N : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 1 / (N : ℝ) := Real.sqrt_sq (by positivity)

/-! ### The gap `‖g‖² - ‖P^* g‖² ≥ ‖g‖²/(2N⁴)` -/

/-- `‖g‖² - ‖P^* g‖² ≥ ‖g‖²/(2N⁴)` for a continuous periodic mean-zero `g` (the end of Step 3 of
the proof of Lemma 8.4 of the paper). -/
private theorem norm_sq_integral_smul_rows_le {P : Lp ℝ 2 (volume.restrict unitCube) →ₗ[ℝ]
      (Vec 2 → ℝ)} {k : Vec 2 → Lp ℝ 2 (volume.restrict unitCube)}
    (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x) (hkc : Continuous k) {s C : ℝ} (hs : 0 < s) (hC : 1 ≤ C)
    (hpos : ∀ f : Lp ℝ 2 (volume.restrict unitCube),
      (∀ᵐ x ∂(volume.restrict unitCube), 0 ≤ f x) → ∀ x, 0 ≤ P f x)
    (hone : ∀ f : Lp ℝ 2 (volume.restrict unitCube),
      (f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] (fun _ => 1) → ∀ x, P f x = 1)
    (hmass : ∀ f : Lp ℝ 2 (volume.restrict unitCube),
      ∫ x in unitCube, P f x = ∫ x in unitCube, f x)
    (hhol : ∀ f x y, |P f x - P f y| ≤ C * torusDist x y ^ s * ‖f‖)
    {g : Vec 2 → ℝ} (hg : Continuous g) (hgp : IsZ2Periodic g)
    (hmean : ∫ x in unitCube, g x = 0) :
    ‖∫ x in unitCube, g x • k x‖ ^ 2 ≤
      (1 - 1 / (2 * (⌈C ^ (1 / s)⌉₊ : ℝ) ^ 4)) * ∫ x in unitCube, g x ^ 2 := by
  set N : ℕ := ⌈C ^ (1 / s)⌉₊ with hNdef
  have hN : 1 ≤ N := one_le_ceil_rpow hC
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hC0 : 0 ≤ C := by linarith
  have hH : Continuous fun p : Vec 2 × Vec 2 => ⟪k p.1, k p.2⟫_ℝ :=
    (hkc.comp continuous_fst).inner (hkc.comp continuous_snd)
  -- the kernel integrand `F x y = H(x,y) |g(x) - g(y)|²`
  have hFc : Continuous fun p : Vec 2 × Vec 2 => ⟪k p.1, k p.2⟫_ℝ * (g p.1 - g p.2) ^ 2 :=
    hH.mul (((hg.comp continuous_fst).sub (hg.comp continuous_snd)).pow 2)
  have hGc : Continuous fun p : Vec 2 × Vec 2 => (g (p.1 + p.2) - g p.1) ^ 2 :=
    ((hg.comp (continuous_fst.add continuous_snd)).sub (hg.comp continuous_fst)).pow 2
  have hQsub : (Set.pi Set.univ
      (fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ))))) ⊆
      Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    have h : 1 / (2 * (N : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [(by exact_mod_cast hN : (1 : ℝ) ≤ N)])
    exact Set.pi_mono fun _ _ => Set.Icc_subset_Icc (neg_le_neg h) h
  -- the first line of the gap estimate, for fixed `x`
  have hstep1 : ∀ x, 1 / 2 * ∫ w in Set.pi Set.univ
        (fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ)))),
        (g (x + w) - g x) ^ 2 ≤
      ∫ y in unitCube, ⟪k x, k y⟫_ℝ * (g x - g y) ^ 2 := by
    intro x
    have hFper : IsZ2Periodic fun y => ⟪k x, k y⟫_ℝ * (g x - g y) ^ 2 := fun n y => by
      simp only [rows_add_latticeShift hk hs hhol y n, hgp n y]
    have hcw : Continuous fun w => ⟪k x, k (x + w)⟫_ℝ * (g x - g (x + w)) ^ 2 :=
      hFc.comp (continuous_const.prodMk (continuous_const.add continuous_id))
    have hcw' : Continuous fun w => 1 / 2 * (g (x + w) - g x) ^ 2 :=
      continuous_const.mul (hGc.comp (continuous_const.prodMk continuous_id))
    rw [integral_unitCube_eq_centredBox_add hFper x, ← integral_const_mul]
    calc ∫ w in Set.pi Set.univ
          (fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ)))),
          1 / 2 * (g (x + w) - g x) ^ 2
        ≤ ∫ w in Set.pi Set.univ
          (fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ)))),
          ⟪k x, k (x + w)⟫_ℝ * (g x - g (x + w)) ^ 2 := by
          refine setIntegral_mono_on (hcw'.continuousOn.integrableOn_compact (box_isCompact _))
            (hcw.continuousOn.integrableOn_compact (box_isCompact _)) (box_measurableSet _)
            fun w hw => ?_
          have hd := torusDist_add_le_of_mem_box hN x w hw
          have hxy : C * torusDist x (x + w) ^ s ≤ 1 :=
            mul_rpow_le_one_of_le_inv_ceil hs hC (torusDist_nonneg_op x (x + w)) hd
          have hhalf := half_le_inner_rows hk hC0 hone hhol hxy
          have hsq : (g x - g (x + w)) ^ 2 = (g (x + w) - g x) ^ 2 := by ring
          rw [hsq]
          exact mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)
      _ ≤ ∫ w in Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)),
          ⟪k x, k (x + w)⟫_ℝ * (g x - g (x + w)) ^ 2 :=
          setIntegral_mono_set (hcw.continuousOn.integrableOn_compact (box_isCompact _))
            (Filter.Eventually.of_forall fun w =>
              mul_nonneg (inner_rows_nonneg hk hpos x (x + w)) (sq_nonneg _))
            hQsub.eventuallyLE
  -- the gap estimate integrated in `x`, Fubini, and the torus inequality
  have hprodQN := integrable_unitCube_prod_box hGc (1 / (2 * (N : ℝ)))
  have hstep2 : 1 / 2 * ∫ w in Set.pi Set.univ
        (fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ)))),
        ∫ x in unitCube, (g (x + w) - g x) ^ 2 ≤
      ∫ x in unitCube, ∫ y in unitCube, ⟪k x, k y⟫_ℝ * (g x - g y) ^ 2 := by
    have hswap := integral_integral_swap (f := fun x w => (g (x + w) - g x) ^ 2) hprodQN
    rw [← hswap, ← integral_const_mul]
    exact integral_mono (hprodQN.integral_prod_left.const_mul _)
      (integrable_unitCube_prod_of_continuous hFc).integral_prod_left hstep1
  have h12 := integral_sq_sub_norm_sq_integral_smul_rows hk hkc hone hmass hg
  have h14 := integral_sq_le_of_small_translates hg hgp hmean hN
  have hN4 : (0 : ℝ) < (N : ℝ) ^ 4 := pow_pos hNpos 4
  set G := ∫ x in unitCube, g x ^ 2 with hG
  set I := ∫ w in Set.pi Set.univ
        (fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ)))),
        ∫ x in unitCube, (g (x + w) - g x) ^ 2 with hI
  have hfrac : G / (2 * (N : ℝ) ^ 4) ≤ I / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hexp : (1 - 1 / (2 * (N : ℝ) ^ 4)) * G = G - G / (2 * (N : ℝ) ^ 4) := by
    field_simp
  rw [hexp]
  linarith

/-- **Operator lemma**, from which Lemma 8.4 of the paper follows. A linear `P` from `L²(𝕋²)` to continuous functions
that is positive, fixes `1`, preserves the integral and satisfies the sup and `s`-Hölder bounds
with constant `C ≥ 1` contracts mean-zero functions:
`‖P f‖₂² ≤ (1 - 1/(2N⁴)) ‖f‖₂²` with `N = ⌈C^{1/s}⌉`. -/
theorem integral_sq_le_of_positive_holder_operator {s C : ℝ} (hs : 0 < s) (hC : 1 ≤ C)
    (P : Lp ℝ 2 (volume.restrict unitCube) →ₗ[ℝ] (Vec 2 → ℝ))
    (hcont : ∀ f, Continuous (P f))
    (hpos : ∀ f : Lp ℝ 2 (volume.restrict unitCube),
      (∀ᵐ x ∂(volume.restrict unitCube), 0 ≤ f x) → ∀ x, 0 ≤ P f x)
    (hone : ∀ f : Lp ℝ 2 (volume.restrict unitCube),
      (f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] (fun _ => 1) → ∀ x, P f x = 1)
    (hmass : ∀ f : Lp ℝ 2 (volume.restrict unitCube),
      ∫ x in unitCube, P f x = ∫ x in unitCube, f x)
    (hsup : ∀ f x, |P f x| ≤ C * ‖f‖)
    (hhol : ∀ f x y, |P f x - P f y| ≤ C * torusDist x y ^ s * ‖f‖)
    (f : Lp ℝ 2 (volume.restrict unitCube)) (hf : ∫ x in unitCube, f x = 0) :
    ∫ x in unitCube, P f x ^ 2 ≤ (1 - 1 / (2 * (⌈C ^ (1 / s)⌉₊ : ℝ) ^ 4)) * ‖f‖ ^ 2 := by
  obtain ⟨k, hk⟩ := exists_riesz_rows hsup
  have hkc := continuous_rows hk hs (by linarith) hhol
  have h15 := norm_sq_integral_smul_rows_le hk hkc hs hC hpos hone hmass hhol (hcont f)
    (isZ2Periodic_of_torus_holder hs hhol f) ((hmass f).trans hf)
  have hadj : ⟪∫ x in unitCube, P f x • k x, f⟫_ℝ = ∫ x in unitCube, P f x ^ 2 := by
    rw [inner_integral_smul_rows hk hkc (hcont f) f]
    simp_rw [sq]
  have hcs : ∫ x in unitCube, P f x ^ 2 ≤ ‖∫ x in unitCube, P f x • k x‖ * ‖f‖ :=
    hadj ▸ real_inner_le_norm _ _
  have hN : (1 : ℝ) ≤ ⌈C ^ (1 / s)⌉₊ := by exact_mod_cast one_le_ceil_rpow hC
  have hθ : 0 ≤ 1 - 1 / (2 * (⌈C ^ (1 / s)⌉₊ : ℝ) ^ 4) := by
    have h1 : (1 : ℝ) ≤ (⌈C ^ (1 / s)⌉₊ : ℝ) ^ 4 := one_le_pow₀ hN
    have h2 : 1 / (2 * (⌈C ^ (1 / s)⌉₊ : ℝ) ^ 4) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  exact le_mul_sq_of_le_mul_of_sq_le (integral_nonneg fun _ => sq_nonneg _) hθ hcs h15

end AVRegularity.Applications.Dissipation

end
