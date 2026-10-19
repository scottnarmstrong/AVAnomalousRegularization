-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.RetainedAssign
import AVRegularity.CycleWords.MixedWords.BlochContinuity
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Order.Group.Lattice

@[expose] public section

section
open MeasureTheory Homogenization Filter AVRegularity.Sobolev
open scoped ENNReal Topology
namespace AVRegularity.CycleWords.Assembly

/-! # Leibniz bounds along a coordinate direction

Iterated directional derivatives `∂_i^j` are iterated derivatives of the restriction to the line
`t ↦ θ + t e_i` (`iterate_dirDeriv_eq_iteratedDeriv`), so the one-dimensional Leibniz bound
applies (`norm_iterate_dirDeriv_smul_le`); the pure partials of the amplitude jet norm are these
iterates (`thetaPartial_eq_iterate_zero`, `thetaPartial_eq_iterate_one`). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_dirDeriv {n : ℕ} {X : Vec 2 → E} (hX : ContDiff ℝ (n + 1 : ℕ) X) (i : Fin 2) :
    ContDiff ℝ n (dirDeriv i X) :=
  (hX.fderiv_right (m := n) (by push_cast; exact le_rfl)).clm_apply contDiff_const

theorem contDiff_iterate_dirDeriv {n : ℕ} {X : Vec 2 → E} (i : Fin 2) :
    ∀ {j : ℕ}, ContDiff ℝ (n + j : ℕ) X → ContDiff ℝ n ((dirDeriv i)^[j] X)
  | 0, hX => hX
  | j + 1, hX => by
    rw [Function.iterate_succ_apply']
    exact contDiff_dirDeriv (contDiff_iterate_dirDeriv (n := n + 1) i (j := j)
      (by rwa [show n + 1 + j = n + (j + 1) by omega])) i

theorem hasDerivAt_line (θ : Vec 2) (i : Fin 2) (s : ℝ) :
    HasDerivAt (fun t : ℝ => θ + t • basisVec i) (basisVec i) s := by
  simpa using ((hasDerivAt_id s).smul_const (basisVec i)).const_add θ

/-- Directional iterates are iterated derivatives along the coordinate line. -/
theorem iterate_dirDeriv_eq_iteratedDeriv {J : ℕ} {X : Vec 2 → E} (hX : ContDiff ℝ J X)
    (i : Fin 2) (θ : Vec 2) :
    ∀ j ≤ J, iteratedDeriv j (fun t : ℝ => X (θ + t • basisVec i)) =
      fun s => (dirDeriv i)^[j] X (θ + s • basisVec i)
  | 0, _ => by simp
  | j + 1, hj => by
    rw [iteratedDeriv_succ, iterate_dirDeriv_eq_iteratedDeriv hX i θ j (by omega)]
    funext s
    have hc : ContDiff ℝ (1 : ℕ) ((dirDeriv i)^[j] X) :=
      contDiff_iterate_dirDeriv (n := 1) i (j := j)
        (hX.of_le (by exact_mod_cast (show 1 + j ≤ J by omega)))
    have hd : DifferentiableAt ℝ ((dirDeriv i)^[j] X) (θ + s • basisVec i) :=
      hc.differentiable (by norm_num) _
    have h := (hd.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_line θ i s)).deriv
    rw [Function.iterate_succ_apply']
    exact h

theorem iterate_dirDeriv_apply_eq {J : ℕ} {Y : Vec 2 → E} (hY : ContDiff ℝ J Y) (i : Fin 2)
    (θ : Vec 2) {l : ℕ} (hl : l ≤ J) :
    (dirDeriv i)^[l] Y θ = iteratedDeriv l (fun t : ℝ => Y (θ + t • basisVec i)) 0 := by
  rw [iterate_dirDeriv_eq_iteratedDeriv hY i θ l hl]
  simp

/-- **Leibniz bound along a coordinate direction.** -/
theorem norm_iterate_dirDeriv_smul_le {J : ℕ} {φ : Vec 2 → ℝ} (hφ : ContDiff ℝ J φ)
    {X : Vec 2 → E} (hX : ContDiff ℝ J X) (i : Fin 2) {j : ℕ} (hj : j ≤ J) (θ : Vec 2) :
    ‖(dirDeriv i)^[j] (fun θ => φ θ • X θ) θ‖ ≤
      ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * |(dirDeriv i)^[l] φ θ| *
        ‖(dirDeriv i)^[j - l] X θ‖ := by
  have hpath : ContDiff ℝ J fun t : ℝ => θ + t • basisVec i :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hφ₁ : ContDiff ℝ J fun t : ℝ => φ (θ + t • basisVec i) := hφ.comp hpath
  have hX₁ : ContDiff ℝ J fun t : ℝ => X (θ + t • basisVec i) := hX.comp hpath
  rw [iterate_dirDeriv_apply_eq (Y := fun θ => φ θ • X θ) (hφ.smul hX) i θ hj,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine (norm_iteratedFDeriv_smul_le hφ₁ hX₁ 0 (by exact_mod_cast hj)).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlj : l ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    ← iterate_dirDeriv_apply_eq hφ i θ (hlj.trans hj),
    ← iterate_dirDeriv_apply_eq hX i θ ((Nat.sub_le j l).trans hj), Real.norm_eq_abs]

theorem orderedDerivative_const_word (i : Fin 2) (Y : Vec 2 → E) :
    ∀ j : ℕ, orderedDerivative (fun _ : Fin j => i) Y = (dirDeriv i)^[j] Y
  | 0 => AVRegularity.orderedDerivative_zero _ _
  | j + 1 => by
    rw [AVRegularity.orderedDerivative_succ, orderedDerivative_const_word i Y j,
      Function.iterate_succ_apply']
    rfl

/-- The pure partial `∂_{θ_0}^l` of the jet norm is the directional iterate. -/
theorem thetaPartial_eq_iterate_zero {l : ℕ} {X : Vec 2 → E} (hX : ContDiff ℝ l X)
    (θ : Vec 2) : thetaPartial l 0 X θ = (dirDeriv 0)^[l] X θ := by
  rw [← orderedDerivative_const_word,
    AVRegularity.orderedDerivative_eq_iteratedFDeriv _ (by exact_mod_cast hX)]
  unfold thetaPartial
  congr 1
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => k.elim0) k
  rw [Fin.append_left]

/-- The pure partial `∂_{θ_1}^l` of the jet norm is the directional iterate. -/
theorem thetaPartial_eq_iterate_one {l : ℕ} {X : Vec 2 → E} (hX : ContDiff ℝ l X)
    (θ : Vec 2) : thetaPartial 0 l X θ = (dirDeriv 1)^[l] X θ := by
  rw [← orderedDerivative_const_word,
    AVRegularity.orderedDerivative_eq_iteratedFDeriv _ (by exact_mod_cast hX)]
  unfold thetaPartial
  have hv : Fin.append (fun _ : Fin 0 => basisVec (0 : Fin 2))
      (fun _ : Fin l => basisVec (1 : Fin 2)) = fun _ => basisVec 1 := by
    funext k
    refine Fin.addCases (fun k => k.elim0) (fun k => ?_) k
    rw [Fin.append_right]
  rw [hv]
  have key : ∀ n : ℕ, n = l → iteratedFDeriv ℝ n X θ (fun _ => basisVec (1 : Fin 2)) =
      iteratedFDeriv ℝ l X θ (fun _ => basisVec (1 : Fin 2)) := by
    rintro n rfl
    rfl
  exact key _ (Nat.zero_add l)

/-- The bound `[l ≤ a] (a+1)^a ρ^{a-l}` of the derivatives of a monomial of degree `a`. -/
noncomputable def monoBound (a l : ℕ) (ρ : ℝ) : ℝ :=
  if l ≤ a then ((a : ℝ) + 1) ^ a * ρ ^ (a - l) else 0

theorem monoBound_step_zero (a : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ρ * monoBound a 0 ρ ≤ monoBound (a + 1) 0 ρ := by
  simp only [monoBound, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  push_cast
  have h1 : ((a : ℝ) + 1) ^ a ≤ ((a : ℝ) + 1 + 1) ^ (a + 1) :=
    (pow_le_pow_left₀ (by positivity) (by linarith) a).trans
      (pow_le_pow_right₀ (by linarith) (Nat.le_succ a))
  calc ρ * (((a : ℝ) + 1) ^ a * ρ ^ a) = ((a : ℝ) + 1) ^ a * ρ ^ (a + 1) := by ring
    _ ≤ ((a : ℝ) + 1 + 1) ^ (a + 1) * ρ ^ (a + 1) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)

theorem monoBound_step_succ (a l : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ρ * monoBound a (l + 1) ρ + ((l + 1 : ℕ) : ℝ) * monoBound a l ρ ≤
      monoBound (a + 1) (l + 1) ρ := by
  unfold monoBound
  have hA : 0 ≤ ((a : ℝ) + 1) ^ a := by positivity
  rcases lt_trichotomy (l + 1) (a + 1) with h | h | h
  · have h1 : l + 1 ≤ a := by omega
    have h2 : l ≤ a := by omega
    have h3 : l + 1 ≤ a + 1 := by omega
    simp only [h1, h2, h3, ↓reduceIte]
    have e1 : ρ * ρ ^ (a - (l + 1)) = ρ ^ (a - l) := by
      rw [← pow_succ']
      congr 1
      omega
    have e2 : a + 1 - (l + 1) = a - l := by omega
    rw [e2]
    have hc : ((l + 1 : ℕ) : ℝ) + 1 ≤ (a : ℝ) + 1 + 1 := by
      have : (l : ℝ) + 1 ≤ a := by exact_mod_cast h1
      push_cast
      linarith
    have hpow : ((a : ℝ) + 1) ^ a ≤ ((a : ℝ) + 1 + 1) ^ a :=
      pow_le_pow_left₀ (by positivity) (by linarith) a
    calc ρ * (((a : ℝ) + 1) ^ a * ρ ^ (a - (l + 1))) +
          ((l + 1 : ℕ) : ℝ) * (((a : ℝ) + 1) ^ a * ρ ^ (a - l))
        = (((l + 1 : ℕ) : ℝ) + 1) * ((a : ℝ) + 1) ^ a * ρ ^ (a - l) := by
          rw [← e1]
          ring
      _ ≤ ((a : ℝ) + 1 + 1) * ((a : ℝ) + 1 + 1) ^ a * ρ ^ (a - l) := by
          gcongr
      _ = (((a + 1 : ℕ) : ℝ) + 1) ^ (a + 1) * ρ ^ (a - l) := by
          push_cast
          ring
  · have h1 : ¬ (l + 1 ≤ a) := by omega
    have h2 : l ≤ a := by omega
    have h3 : l + 1 ≤ a + 1 := le_of_eq h
    simp only [h1, h2, h3, ↓reduceIte]
    have hl : l = a := by omega
    subst hl
    simp only [Nat.sub_self, pow_zero, mul_one, mul_zero, zero_add]
    push_cast
    calc ((l : ℝ) + 1) * ((l : ℝ) + 1) ^ l = ((l : ℝ) + 1) ^ (l + 1) := by ring
      _ ≤ ((l : ℝ) + 1 + 1) ^ (l + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
  · have h1 : ¬ (l + 1 ≤ a) := by omega
    have h2 : ¬ (l ≤ a) := by omega
    have h3 : ¬ (l + 1 ≤ a + 1) := by omega
    simp only [h1, h2, h3, ↓reduceIte]
    simp

theorem dirDeriv_coord (i k : Fin 2) :
    dirDeriv i (fun θ : Vec 2 => θ k) = fun _ => basisVec i k := by
  funext θ
  have h : HasFDerivAt (fun θ : Vec 2 => θ k) (ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ) θ :=
    hasFDerivAt_apply k θ
  simp only [dirDeriv, h.fderiv, ContinuousLinearMap.proj_apply]

theorem dirDeriv_const (i : Fin 2) (c : E) : dirDeriv i (fun _ : Vec 2 => c) = 0 := by
  funext θ
  simp [dirDeriv]

theorem iterate_dirDeriv_zero (i : Fin 2) : ∀ n : ℕ, (dirDeriv i)^[n] (0 : Vec 2 → E) = 0
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', iterate_dirDeriv_zero i n]
    exact dirDeriv_const i 0

theorem iterate_dirDeriv_const_succ (i : Fin 2) (c : E) (n : ℕ) :
    (dirDeriv i)^[n + 1] (fun _ : Vec 2 => c) = 0 := by
  rw [Function.iterate_succ_apply, dirDeriv_const, iterate_dirDeriv_zero]

theorem abs_iterate_dirDeriv_coord_le (i k : Fin 2) (θ : Vec 2) (l : ℕ) :
    |(dirDeriv i)^[l] (fun θ : Vec 2 => θ k) θ| ≤
      if l = 0 then ‖θ‖ else if l = 1 then 1 else 0 := by
  rcases l with _ | _ | l
  · simp only [Function.iterate_zero, id, ↓reduceIte]
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm θ k
  · show |dirDeriv i (fun θ : Vec 2 => θ k) θ| ≤ _
    rw [dirDeriv_coord]
    simp only [basisVec_apply]
    split_ifs <;> simp_all
  · rw [show l + 1 + 1 = (l + 1) + 1 from rfl, Function.iterate_succ_apply, dirDeriv_coord,
      iterate_dirDeriv_const_succ]
    simp

/-- **Derivatives of a word monomial** along a coordinate direction. -/
theorem abs_iterate_dirDeriv_monomial_le : ∀ {a : ℕ} (w : DerivativeWord2 a) (i : Fin 2)
    (θ : Vec 2) (l : ℕ), |(dirDeriv i)^[l] (wordMonomial w) θ| ≤ monoBound a l ‖θ‖
  | 0, w, i, θ, l => by
    have h1 : wordMonomial w = fun _ => (1 : ℝ) := by
      funext θ
      simp [wordMonomial]
    rw [h1]
    rcases l with _ | l
    · simp [monoBound]
    · rw [iterate_dirDeriv_const_succ]
      simp [monoBound]
  | a + 1, w, i, θ, l => by
    set k := w (Fin.last a)
    set w₀ : DerivativeWord2 a := fun i => w i.castSucc
    have hw : wordMonomial w = fun θ => θ k • wordMonomial w₀ θ := by
      funext θ
      rw [wordMonomial_succ, smul_eq_mul]
    have hρ : 0 ≤ ‖θ‖ := norm_nonneg θ
    have hlb := norm_iterate_dirDeriv_smul_le (J := l) (contDiff_apply ℝ ℝ k)
      ((wordMonomial_contDiff w₀).of_le (by exact_mod_cast le_top)) i le_rfl θ
    rw [hw, ← Real.norm_eq_abs]
    refine hlb.trans ?_
    have hterm : ∀ l' ∈ Finset.range (l + 1), (l.choose l' : ℝ) *
        |(dirDeriv i)^[l'] (fun θ : Vec 2 => θ k) θ| *
          ‖(dirDeriv i)^[l - l'] (wordMonomial w₀) θ‖ ≤
        (l.choose l' : ℝ) * (if l' = 0 then ‖θ‖ else if l' = 1 then 1 else 0) *
          monoBound a (l - l') ‖θ‖ := fun l' _ => by
      gcongr
      · exact abs_iterate_dirDeriv_coord_le i k θ l'
      · rw [Real.norm_eq_abs]
        exact abs_iterate_dirDeriv_monomial_le w₀ i θ (l - l')
    refine (Finset.sum_le_sum hterm).trans ?_
    rcases l with _ | l
    · simp only [zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_mul,
        ↓reduceIte, Nat.sub_zero]
      exact monoBound_step_zero a hρ
    · rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hz : ∀ l' ∈ Finset.range l, ((l + 1).choose (l' + 1 + 1) : ℝ) *
          (if l' + 1 + 1 = 0 then ‖θ‖ else if l' + 1 + 1 = 1 then 1 else 0) *
            monoBound a (l + 1 - (l' + 1 + 1)) ‖θ‖ = 0 := fun l' _ => by simp
      rw [Finset.sum_eq_zero hz, zero_add]
      simp only [Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_one, one_mul,
        zero_add, one_ne_zero, ↓reduceIte, Nat.sub_zero, Nat.add_sub_cancel, mul_one]
      have := monoBound_step_succ a l hρ
      linarith

theorem pow_mul_pow_le_bracket {ϖ ρ : ℝ} (hϖ : 0 < ϖ) (hρ : 0 ≤ ρ) {a l : ℕ} (hl : l ≤ a) :
    ϖ ^ l * ρ ^ (a - l) ≤ ϖ ^ a * (1 + ρ / ϖ) ^ a := by
  have e : ϖ ^ l * ρ ^ (a - l) = ϖ ^ a * (ρ / ϖ) ^ (a - l) := by
    have hpa : ϖ ^ a = ϖ ^ l * ϖ ^ (a - l) := by rw [← pow_add, Nat.add_sub_cancel' hl]
    rw [hpa, div_pow]
    field_simp
  rw [e]
  have h1 : 0 ≤ ρ / ϖ := div_nonneg hρ hϖ.le
  gcongr
  calc (ρ / ϖ) ^ (a - l) ≤ (1 + ρ / ϖ) ^ (a - l) := pow_le_pow_left₀ h1 (by linarith) _
    _ ≤ (1 + ρ / ϖ) ^ a := pow_le_pow_right₀ (by linarith) (Nat.sub_le a l)

/-- **Pointwise weighted bound** for a monomial times an amplitude. -/
theorem weighted_monomial_bound {ϖ : ℝ} (hϖ : 0 < ϖ) {j : ℕ} {X : Vec 2 → E}
    (hX : ContDiff ℝ j X) (i : Fin 2) {a : ℕ} (w : DerivativeWord2 a) (θ : Vec 2) :
    ϖ ^ j * ‖(dirDeriv i)^[j] (fun θ => wordMonomial w θ • X θ) θ‖ ≤
      ϖ ^ a * (2 ^ j * ((a : ℝ) + 1) ^ a * (1 + ‖θ‖ / ϖ) ^ a) *
        ∑ l ∈ Finset.range (j + 1), ϖ ^ l * ‖(dirDeriv i)^[l] X θ‖ := by
  have hρ : 0 ≤ ‖θ‖ := norm_nonneg θ
  have hL := norm_iterate_dirDeriv_smul_le (J := j)
    ((wordMonomial_contDiff w).of_le (by exact_mod_cast le_top)) hX i le_rfl θ
  set K : ℝ := ϖ ^ a * (2 ^ j * ((a : ℝ) + 1) ^ a * (1 + ‖θ‖ / ϖ) ^ a) with hK
  have hterm : ∀ l ∈ Finset.range (j + 1), ϖ ^ j * ((j.choose l : ℝ) *
      |(dirDeriv i)^[l] (wordMonomial w) θ| * ‖(dirDeriv i)^[j - l] X θ‖) ≤
      K * (ϖ ^ (j - l) * ‖(dirDeriv i)^[j - l] X θ‖) := by
    intro l hl
    have hlj : l ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have hm := abs_iterate_dirDeriv_monomial_le w i θ l
    have hc : (j.choose l : ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.choose_le_two_pow j l
    have hn := norm_nonneg ((dirDeriv i)^[j - l] X θ)
    have hsplit : ϖ ^ j = ϖ ^ (j - l) * ϖ ^ l := by rw [← pow_add, Nat.sub_add_cancel hlj]
    by_cases hla : l ≤ a
    · have hmb : monoBound a l ‖θ‖ = ((a : ℝ) + 1) ^ a * ‖θ‖ ^ (a - l) := by
        simp [monoBound, hla]
      rw [hmb] at hm
      have hb := pow_mul_pow_le_bracket hϖ hρ hla
      calc ϖ ^ j * ((j.choose l : ℝ) * |(dirDeriv i)^[l] (wordMonomial w) θ| *
            ‖(dirDeriv i)^[j - l] X θ‖)
          ≤ ϖ ^ j * (2 ^ j * (((a : ℝ) + 1) ^ a * ‖θ‖ ^ (a - l)) *
            ‖(dirDeriv i)^[j - l] X θ‖) := by
            gcongr
        _ = 2 ^ j * ((a : ℝ) + 1) ^ a * (ϖ ^ l * ‖θ‖ ^ (a - l)) *
            (ϖ ^ (j - l) * ‖(dirDeriv i)^[j - l] X θ‖) := by rw [hsplit]; ring
        _ ≤ 2 ^ j * ((a : ℝ) + 1) ^ a * (ϖ ^ a * (1 + ‖θ‖ / ϖ) ^ a) *
            (ϖ ^ (j - l) * ‖(dirDeriv i)^[j - l] X θ‖) := by gcongr
        _ = K * (ϖ ^ (j - l) * ‖(dirDeriv i)^[j - l] X θ‖) := by rw [hK]; ring
    · have hmb : monoBound a l ‖θ‖ = 0 := by simp [monoBound, hla]
      rw [hmb] at hm
      have h0 : |(dirDeriv i)^[l] (wordMonomial w) θ| = 0 := le_antisymm hm (abs_nonneg _)
      rw [h0, mul_zero, zero_mul, mul_zero]
      positivity
  calc ϖ ^ j * ‖(dirDeriv i)^[j] (fun θ => wordMonomial w θ • X θ) θ‖
      ≤ ϖ ^ j * ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
          |(dirDeriv i)^[l] (wordMonomial w) θ| * ‖(dirDeriv i)^[j - l] X θ‖ :=
        mul_le_mul_of_nonneg_left hL (by positivity)
    _ ≤ ∑ l ∈ Finset.range (j + 1), K * (ϖ ^ (j - l) * ‖(dirDeriv i)^[j - l] X θ‖) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hterm
    _ = K * ∑ l ∈ Finset.range (j + 1), ϖ ^ l * ‖(dirDeriv i)^[l] X θ‖ := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_range_reflect (fun l => ϖ ^ l * ‖(dirDeriv i)^[l] X θ‖) (j + 1)

/-- Minkowski for weighted pairs over a finite sum. -/
theorem weighted_sum_minkowski {ι κ : Type*} [Fintype ι] (s : Finset κ) (w : ι → ℝ≥0∞)
    (p q : κ → ι → ℝ≥0∞) :
    (∑ x, w x * ((∑ l ∈ s, p l x) ^ 2 + (∑ l ∈ s, q l x) ^ 2)) ^ (1 / 2 : ℝ) ≤
      ∑ l ∈ s, (∑ x, w x * (p l x ^ 2 + q l x ^ 2)) ^ (1 / 2 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (weighted_pair_minkowski w (p a) (q a) (fun x => ∑ l ∈ s, p l x)
      (fun x => ∑ l ∈ s, q l x)).trans (add_le_add le_rfl ih)

/-- The multi-index of the pure partial `∂_{θ_i}^l`. -/
def dirIndex (i : Fin 2) (l : ℕ) : ℕ × ℕ := if i = 0 then (l, 0) else (0, l)

theorem dirIndex_mem {i : Fin 2} {l m : ℕ} (hl : l ≤ m) : dirIndex i l ∈ momentIndices m := by
  unfold dirIndex momentIndices
  split_ifs <;> simp [hl]

theorem dirIndex_factorial (i : Fin 2) (l : ℕ) :
    ((dirIndex i l).1.factorial * (dirIndex i l).2.factorial : ℕ) = l.factorial := by
  unfold dirIndex
  split_ifs <;> simp

theorem dirIndex_sum (i : Fin 2) (l : ℕ) : (dirIndex i l).1 + (dirIndex i l).2 = l := by
  unfold dirIndex
  split_ifs <;> simp

theorem thetaPartial_dirIndex {i : Fin 2} {l : ℕ} {X : Vec 2 → E} (hX : ContDiff ℝ l X)
    (θ : Vec 2) :
    thetaPartial (dirIndex i l).1 (dirIndex i l).2 X θ = (dirDeriv i)^[l] X θ := by
  fin_cases i
  · simp only [dirIndex, Fin.zero_eta, Fin.isValue, ↓reduceIte]
    exact thetaPartial_eq_iterate_zero hX θ
  · simp only [dirIndex, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    exact thetaPartial_eq_iterate_one hX θ

section Jet

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- One pure-direction layer of the amplitude jet norm. -/
theorem dirLayer_le_amplitudeJetNorm (π : ι → ℝ) {m : ℕ} {ϖ : ℝ} (hϖ : 0 ≤ ϖ)
    {A B : ∀ x, Vec 2 → h x} (hA : ∀ x, ContDiff ℝ m (A x)) (hB : ∀ x, ContDiff ℝ m (B x))
    (i : Fin 2) {l : ℕ} (hl : l ≤ m) (θ : Vec 2) :
    (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (ENNReal.ofReal (ϖ ^ l * ‖(dirDeriv i)^[l] (A x) θ‖) ^ 2 +
          ENNReal.ofReal (ϖ ^ l * ‖(dirDeriv i)^[l] (B x) θ‖) ^ 2)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (l.factorial : ℝ) * amplitudeJetNorm π m ϖ A B θ := by
  have hAl : ∀ x, ContDiff ℝ l (A x) := fun x => (hA x).of_le (by exact_mod_cast hl)
  have hBl : ∀ x, ContDiff ℝ l (B x) := fun x => (hB x).of_le (by exact_mod_cast hl)
  set T := (∑ x, ENNReal.ofReal ((π x)⁻¹) *
    (ENNReal.ofReal (‖thetaPartial (dirIndex i l).1 (dirIndex i l).2 (A x) θ‖ ^ 2) +
      ENNReal.ofReal (‖thetaPartial (dirIndex i l).1 (dirIndex i l).2 (B x) θ‖ ^ 2))) ^
        (1 / 2 : ℝ) with hT
  have hsingle : ENNReal.ofReal (ϖ ^ l / (l.factorial : ℝ)) * T ≤ amplitudeJetNorm π m ϖ A B θ := by
    have h := Finset.single_le_sum (f := fun β : ℕ × ℕ =>
      ENNReal.ofReal (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
        (∑ x, ENNReal.ofReal ((π x)⁻¹) *
          (ENNReal.ofReal (‖thetaPartial β.1 β.2 (A x) θ‖ ^ 2) +
            ENNReal.ofReal (‖thetaPartial β.1 β.2 (B x) θ‖ ^ 2))) ^ (1 / 2 : ℝ))
      (fun _ _ => zero_le) (dirIndex_mem (i := i) hl)
    simp only [dirIndex_sum, dirIndex_factorial] at h
    exact h
  have hLHS : (∑ x, ENNReal.ofReal ((π x)⁻¹) *
      (ENNReal.ofReal (ϖ ^ l * ‖(dirDeriv i)^[l] (A x) θ‖) ^ 2 +
        ENNReal.ofReal (ϖ ^ l * ‖(dirDeriv i)^[l] (B x) θ‖) ^ 2)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (ϖ ^ l) * T := by
    rw [hT, ← sq_rpow_half (ENNReal.ofReal (ϖ ^ l)), ← ENNReal.mul_rpow_of_nonneg _ _
      (by norm_num), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [thetaPartial_dirIndex (hAl x), thetaPartial_dirIndex (hBl x),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
    ring
  rw [hLHS]
  have hfac : (0 : ℝ) < l.factorial := by exact_mod_cast Nat.factorial_pos l
  calc ENNReal.ofReal (ϖ ^ l) * T
      = ENNReal.ofReal (l.factorial : ℝ) * (ENNReal.ofReal (ϖ ^ l / (l.factorial : ℝ)) * T) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hfac.le, mul_div_cancel₀ _ hfac.ne']
    _ ≤ _ := mul_le_mul' le_rfl hsingle

/-- **The weighted amplitudes of `z_i^j D^w` by the amplitude jet norm**, pointwise in `θ`. -/
theorem weightedAmp_le_amplitudeJetNorm (π : ι → ℝ) {m : ℕ} {ϖ : ℝ} (hϖ : 0 < ϖ)
    {A B : ∀ x, Vec 2 → h x} (hA : ∀ x, ContDiff ℝ m (A x)) (hB : ∀ x, ContDiff ℝ m (B x))
    (i : Fin 2) {j : ℕ} (hj : j ≤ m) {a : ℕ} (w : DerivativeWord2 a) (θ : Vec 2) :
    (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • A x θ) θ‖) ^ 2 +
          ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • B x θ) θ‖) ^ 2)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (ϖ ^ a * (2 ^ j * ((a : ℝ) + 1) ^ a * (1 + ‖θ‖ / ϖ) ^ a) *
        ((j + 1 : ℕ) * (m.factorial : ℝ))) * amplitudeJetNorm π m ϖ A B θ := by
  set K : ℝ := ϖ ^ a * (2 ^ j * ((a : ℝ) + 1) ^ a * (1 + ‖θ‖ / ϖ) ^ a) with hK
  have hK0 : 0 ≤ K := by positivity
  have hAj : ∀ x, ContDiff ℝ j (A x) := fun x => (hA x).of_le (by exact_mod_cast hj)
  have hBj : ∀ x, ContDiff ℝ j (B x) := fun x => (hB x).of_le (by exact_mod_cast hj)
  set p : ℕ → ι → ℝ≥0∞ := fun l x => ENNReal.ofReal (ϖ ^ l * ‖(dirDeriv i)^[l] (A x) θ‖)
    with hp
  set q : ℕ → ι → ℝ≥0∞ := fun l x => ENNReal.ofReal (ϖ ^ l * ‖(dirDeriv i)^[l] (B x) θ‖)
    with hq
  have hpt : ∀ x (X : Vec 2 → h x), ContDiff ℝ j X →
      ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j] (fun θ => wordMonomial w θ • X θ) θ‖) ≤
        ENNReal.ofReal K * ∑ l ∈ Finset.range (j + 1),
          ENNReal.ofReal (ϖ ^ l * ‖(dirDeriv i)^[l] X θ‖) := by
    intro x X hX
    rw [← ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity), ← ENNReal.ofReal_mul hK0]
    exact ENNReal.ofReal_le_ofReal (weighted_monomial_bound hϖ hX i w θ)
  have hfac : (0 : ℝ) ≤ m.factorial := Nat.cast_nonneg _
  calc (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • A x θ) θ‖) ^ 2 +
          ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • B x θ) θ‖) ^ 2)) ^ (1 / 2 : ℝ)
      ≤ (∑ x, ENNReal.ofReal ((π x)⁻¹) *
          ((ENNReal.ofReal K * ∑ l ∈ Finset.range (j + 1), p l x) ^ 2 +
            (ENNReal.ofReal K * ∑ l ∈ Finset.range (j + 1), q l x) ^ 2)) ^ (1 / 2 : ℝ) := by
        gcongr with x
        · exact hpt x (A x) (hAj x)
        · exact hpt x (B x) (hBj x)
    _ = ENNReal.ofReal K * (∑ x, ENNReal.ofReal ((π x)⁻¹) *
          ((∑ l ∈ Finset.range (j + 1), p l x) ^ 2 +
            (∑ l ∈ Finset.range (j + 1), q l x) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [← sq_rpow_half (ENNReal.ofReal K), ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          Finset.mul_sum, sq_rpow_half]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ ENNReal.ofReal K * ∑ l ∈ Finset.range (j + 1),
          (∑ x, ENNReal.ofReal ((π x)⁻¹) * (p l x ^ 2 + q l x ^ 2)) ^ (1 / 2 : ℝ) := by
        gcongr
        exact weighted_sum_minkowski _ _ p q
    _ ≤ ENNReal.ofReal K * ∑ l ∈ Finset.range (j + 1),
          ENNReal.ofReal (m.factorial : ℝ) * amplitudeJetNorm π m ϖ A B θ := by
        gcongr with l hl
        have hlm : l ≤ m := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)).trans hj
        refine (dirLayer_le_amplitudeJetNorm π hϖ.le hA hB i hlm θ).trans ?_
        gcongr
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul hK0,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))]
        simp only [ENNReal.ofReal_natCast]
        ring

end Jet

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization Filter AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Weighted jets of band-limited families by their amplitude jets

The weight `(1 + ϖ²|z|²)^{m/2}` is at most `3^m (1 + |ϖz₀|^m + |ϖz₁|^m)` (`weight_le`), each
`(ϖ z_i)^j D^w g` is band-limited with amplitudes `ϖ^j ∂_i^j(θ^w A)` up to the rotation, so
Plancherel bounds it by their `L²` norms (`eLpNorm_coordPow_orderedDerivative_le`), and the
inverse-mass sum of those is the `θ`-integral of the pointwise bound by the amplitude jet norm. -/

theorem weight_eq_jbracket_pow (ϖ : ℝ) (m : ℕ) (z : Vec 2) :
    (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) = jbracket (ϖ • z) ^ m := by
  have hu : 0 ≤ 1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by positivity
  have hj : jbracket (ϖ • z) = (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (1 / 2 : ℝ) := by
    unfold jbracket
    rw [Real.sqrt_eq_rpow]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hj, ← Real.rpow_mul_natCast hu]
  congr 1
  ring

theorem weight_le (ϖ : ℝ) (m : ℕ) (z : Vec 2) :
    (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) ≤
      3 ^ m * (1 + |ϖ * z 0| ^ m + |ϖ * z 1| ^ m) := by
  rw [weight_eq_jbracket_pow]
  refine (pow_le_pow_left₀ (jbracket_pos _).le (jbracket_le _) m).trans ?_
  simpa only [Pi.smul_apply, smul_eq_mul] using
    one_add_add_pow_le _ _ (abs_nonneg (ϖ * z 0)) (abs_nonneg (ϖ * z 1)) m

theorem weight_nonneg (ϖ : ℝ) (m : ℕ) (z : Vec 2) :
    0 ≤ (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) :=
  Real.rpow_nonneg (by positivity) _

section Weight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polyWeight_continuous (ϖ : ℝ) (m : ℕ) :
    Continuous fun z : Vec 2 => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) := by
  have h : (fun z : Vec 2 => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2)) =
      fun z => jbracket (ϖ • z) ^ m := funext (weight_eq_jbracket_pow ϖ m)
  rw [h]
  exact (jbracket_contDiff.continuous.comp (continuous_const_smul ϖ)).pow m

/-- **The polynomial weight** by three moment weights. -/
theorem eLpNorm_weight_smul_le (ϖ : ℝ) (m : ℕ) {v : Vec 2 → E}
    (hv : AEStronglyMeasurable v volume) :
    eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) • v z) 2 volume ≤
      ENNReal.ofReal (3 ^ m) * (eLpNorm v 2 volume +
        eLpNorm (fun z => (ϖ * z 0) ^ m • v z) 2 volume +
        eLpNorm (fun z => (ϖ * z 1) ^ m • v z) 2 volume) := by
  have hc0 : Continuous fun z : Vec 2 => (ϖ * z 0) ^ m := by fun_prop
  have hc1 : Continuous fun z : Vec 2 => (ϖ * z 1) ^ m := by fun_prop
  have hm0 := hc0.aestronglyMeasurable.smul hv
  have hm1 := hc1.aestronglyMeasurable.smul hv
  refine (eLpNorm_mono_real ((polyWeight_continuous ϖ m).aestronglyMeasurable.smul hv)
    (g := fun z => 3 ^ m * (‖v z‖ + ‖(ϖ * z 0) ^ m • v z‖ + ‖(ϖ * z 1) ^ m • v z‖))
    fun z => ?_).trans ?_
  · show ‖(1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) • v z‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg ϖ m z)]
    simp only [norm_smul, Real.norm_eq_abs, abs_pow]
    calc (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) * ‖v z‖
        ≤ 3 ^ m * (1 + |ϖ * z 0| ^ m + |ϖ * z 1| ^ m) * ‖v z‖ :=
          mul_le_mul_of_nonneg_right (weight_le ϖ m z) (norm_nonneg _)
      _ = _ := by ring
  · rw [show (fun z => (3 : ℝ) ^ m * (‖v z‖ + ‖(ϖ * z 0) ^ m • v z‖ +
        ‖(ϖ * z 1) ^ m • v z‖)) = (3 : ℝ) ^ m • fun z => ‖v z‖ + ‖(ϖ * z 0) ^ m • v z‖ +
          ‖(ϖ * z 1) ^ m • v z‖ from rfl, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    gcongr
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add
      ((eLpNorm_add_le (by norm_num)).trans (add_le_add (le_of_eq ?_) (le_of_eq ?_)))
      (le_of_eq ?_))
    · exact eLpNorm_norm v hv
    · exact eLpNorm_norm _ hm0
    · exact eLpNorm_norm _ hm1

end Weight

theorem add3_sq_le (a b c : ℝ≥0∞) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have h := ennreal_sum_mul_sq_le Finset.univ (fun _ : Fin 3 => (1 : ℝ≥0∞)) ![a, b, c]
  simp only [Fin.sum_univ_three, one_mul, one_pow, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  calc (a + b + c) ^ 2 ≤ (1 + 1 + 1) * (a ^ 2 + b ^ 2 + c ^ 2) := h
    _ = 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by norm_num

section Plancherel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem IsBandAmp.iterate_monomial {r : ℝ} {m : ℕ} {A : Vec 2 → E} (hA : IsBandAmp r m A)
    (i : Fin 2) {j : ℕ} (hj : j ≤ m) {a : ℕ} (w : DerivativeWord2 a) :
    IsBandAmp r (m - j) ((dirDeriv i)^[j] fun θ => wordMonomial w θ • A θ) :=
  IsBandAmp.iterate_dirDeriv (m := m - j) i
    (by rw [Nat.sub_add_cancel hj]; exact hA.monomial_smul w)

/-- `‖X‖₂² + ‖Y‖₂²` as one lower integral. -/
theorem eLpNorm_sq_add_eq_lintegral {X Y : Vec 2 → E} (hX : Continuous X) (hY : Continuous Y) :
    eLpNorm X 2 volume ^ 2 + eLpNorm Y 2 volume ^ 2 =
      ∫⁻ θ, (ENNReal.ofReal ‖X θ‖ ^ 2 + ENNReal.ofReal ‖Y θ‖ ^ 2) := by
  rw [eLpNorm_two_sq hX.aestronglyMeasurable, eLpNorm_two_sq hY.aestronglyMeasurable,
    ← lintegral_add_left' (f := fun x => ‖X x‖ₑ ^ 2)
      ((ENNReal.continuous_pow 2).comp hX.enorm).measurable.aemeasurable]
  refine lintegral_congr fun θ => ?_
  rw [ofReal_norm, ofReal_norm]

/-- **One weighted derivative term** by Plancherel. -/
theorem eLpNorm_coordPow_orderedDerivative_le {r : ℝ} (hr : 0 ≤ r) {m : ℕ} {A B : Vec 2 → E}
    (hA : IsBandAmp r m A) (hB : IsBandAmp r m B) {ϖ : ℝ} (hϖ : 0 ≤ ϖ) (i : Fin 2) {j : ℕ}
    (hj : j ≤ m) {a : ℕ} (w : DerivativeWord2 a) :
    eLpNorm (fun z => (ϖ * z i) ^ j • orderedDerivative w (ampFun r A B) z) 2 volume ≤
      ENNReal.ofReal (2 * Real.pi) * (∫⁻ θ,
        (ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j] (fun θ => wordMonomial w θ • A θ) θ‖) ^ 2 +
          ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • B θ) θ‖) ^ 2)) ^ (1 / 2 : ℝ) := by
  set U := (dirDeriv i)^[j] fun θ => wordMonomial w θ • A θ with hU
  set V := (dirDeriv i)^[j] fun θ => wordMonomial w θ • B θ with hV
  have hUb : IsBandAmp r 0 U := (hA.iterate_monomial i hj w).of_le (Nat.zero_le _)
  have hVb : IsBandAmp r 0 V := (hB.iterate_monomial i hj w).of_le (Nat.zero_le _)
  have hmem := jRot_mem (fun X : Vec 2 → E => IsBandAmp r 0 X) (fun X hX => hX.neg) (j + a)
    (p := (U, V)) hUb hVb
  have e1 : (fun z => (ϖ * z i) ^ j • orderedDerivative w (ampFun r A B) z) =
      (ϖ ^ j : ℝ) • ampFun r (jRot (j + a) (U, V)).1 (jRot (j + a) (U, V)).2 := by
    funext z
    rw [Pi.smul_apply, mul_pow, mul_smul, coordPow_orderedDerivative_ampFun hr hA hB i hj w z]
  have hP := eLpNorm_ampFun_le hr (fun θ h => ⟨hmem.1.2 θ h, hmem.2.2 θ h⟩) hmem.1.integrableOn
    hmem.2.integrableOn
  have hrot : eLpNorm (jRot (j + a) (U, V)).1 2 volume ^ 2 +
      eLpNorm (jRot (j + a) (U, V)).2 2 volume ^ 2 =
      ∫⁻ θ, (ENNReal.ofReal ‖U θ‖ ^ 2 + ENNReal.ofReal ‖V θ‖ ^ 2) := by
    rw [eLpNorm_sq_add_eq_lintegral hmem.1.1.continuous hmem.2.1.continuous]
    refine lintegral_congr fun θ => ?_
    have h := jRot_norm_sq (j + a) (U, V) θ
    simp only at h
    rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), h,
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
      ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e1, eLpNorm_const_smul, Real.enorm_eq_ofReal (pow_nonneg hϖ j)]
  calc ENNReal.ofReal (ϖ ^ j) * eLpNorm (ampFun r (jRot (j + a) (U, V)).1
        (jRot (j + a) (U, V)).2) 2 volume
      ≤ ENNReal.ofReal (ϖ ^ j) * (ENNReal.ofReal (2 * Real.pi) *
          (∫⁻ θ, (ENNReal.ofReal ‖U θ‖ ^ 2 + ENNReal.ofReal ‖V θ‖ ^ 2)) ^ (1 / 2 : ℝ)) := by
        rw [← hrot]
        exact mul_le_mul' le_rfl hP
    _ = ENNReal.ofReal (2 * Real.pi) * (∫⁻ θ,
          (ENNReal.ofReal (ϖ ^ j * ‖U θ‖) ^ 2 + ENNReal.ofReal (ϖ ^ j * ‖V θ‖) ^ 2)) ^
            (1 / 2 : ℝ) := by
        rw [mul_left_comm]
        congr 1
        rw [← sq_rpow_half (ENNReal.ofReal (ϖ ^ j)), ← ENNReal.mul_rpow_of_nonneg _ _
          (by norm_num), ← lintegral_const_mul' _ _ (by simp)]
        congr 1
        refine lintegral_congr fun θ => ?_
        rw [ENNReal.ofReal_mul (pow_nonneg hϖ j), ENNReal.ofReal_mul (pow_nonneg hϖ j)]
        ring

/-- The `θ`-integral of the squared weighted amplitudes of `z_i^j D^w`. -/
noncomputable def ampR (A B : Vec 2 → E) (ϖ : ℝ) (i : Fin 2) (j : ℕ) {a : ℕ}
    (w : DerivativeWord2 a) : ℝ≥0∞ :=
  ∫⁻ θ, (ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j] (fun θ => wordMonomial w θ • A θ) θ‖) ^ 2 +
    ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j] (fun θ => wordMonomial w θ • B θ) θ‖) ^ 2)

theorem continuous_orderedDerivative_ampFun {r : ℝ} (hr : 0 ≤ r) {m : ℕ} {A B : Vec 2 → E}
    (hA : IsBandAmp r m A) (hB : IsBandAmp r m B) {a : ℕ} (w : DerivativeWord2 a) :
    Continuous (orderedDerivative w (ampFun r A B)) := by
  have hmem := jRot_mem (fun X : Vec 2 → E => IsBandAmp r 0 X) (fun X hX => hX.neg) a
    (p := (fun θ => wordMonomial w θ • A θ, fun θ => wordMonomial w θ • B θ))
    ((hA.of_le (Nat.zero_le m)).monomial_smul w) ((hB.of_le (Nat.zero_le m)).monomial_smul w)
  rw [orderedDerivative_ampFun_eq hr w (hA.of_le (Nat.zero_le m)) (hB.of_le (Nat.zero_le m))]
  exact (ampFun_contDiff hr 0 hmem.1.integrableOn hmem.2.integrableOn).continuous

/-- **One derivative word**: the weighted `L²` norm of `D^w ampFun` by three amplitude
integrals. -/
theorem wordTerm_sq_le {r : ℝ} (hr : 0 ≤ r) {m : ℕ} {A B : Vec 2 → E} (hA : IsBandAmp r m A)
    (hB : IsBandAmp r m B) {ϖ : ℝ} (hϖ : 0 ≤ ϖ) {a : ℕ} (w : DerivativeWord2 a) :
    eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) •
        orderedDerivative w (ampFun r A B) z) 2 volume ^ 2 ≤
      ENNReal.ofReal (3 ^ m) ^ 2 * 3 * ENNReal.ofReal (2 * Real.pi) ^ 2 *
        (ampR A B ϖ 0 0 w + ampR A B ϖ 0 m w + ampR A B ϖ 1 m w) := by
  have hv : AEStronglyMeasurable (orderedDerivative w (ampFun r A B)) volume :=
    (continuous_orderedDerivative_ampFun hr hA hB w).aestronglyMeasurable
  have h1 := eLpNorm_weight_smul_le ϖ m hv
  have h0 : eLpNorm (orderedDerivative w (ampFun r A B)) 2 volume =
      eLpNorm (fun z => (ϖ * z 0) ^ 0 • orderedDerivative w (ampFun r A B) z) 2 volume := by
    congr 1
    funext z
    simp
  have hT : ∀ (i : Fin 2) (j : ℕ), j ≤ m →
      eLpNorm (fun z => (ϖ * z i) ^ j • orderedDerivative w (ampFun r A B) z) 2 volume ^ 2 ≤
        ENNReal.ofReal (2 * Real.pi) ^ 2 * ampR A B ϖ i j w := fun i j hj => by
    have h := eLpNorm_coordPow_orderedDerivative_le hr hA hB hϖ i hj w
    calc eLpNorm (fun z => (ϖ * z i) ^ j • orderedDerivative w (ampFun r A B) z) 2 volume ^ 2
        ≤ (ENNReal.ofReal (2 * Real.pi) * ampR A B ϖ i j w ^ (1 / 2 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h 2
      _ = _ := by rw [mul_pow, rpow_half_sq]
  rw [h0] at h1
  calc eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) •
        orderedDerivative w (ampFun r A B) z) 2 volume ^ 2
      ≤ (ENNReal.ofReal (3 ^ m) *
          (eLpNorm (fun z => (ϖ * z 0) ^ 0 • orderedDerivative w (ampFun r A B) z) 2 volume +
            eLpNorm (fun z => (ϖ * z 0) ^ m • orderedDerivative w (ampFun r A B) z) 2 volume +
            eLpNorm (fun z => (ϖ * z 1) ^ m • orderedDerivative w (ampFun r A B) z) 2
              volume)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    _ ≤ ENNReal.ofReal (3 ^ m) ^ 2 * (3 *
          (ENNReal.ofReal (2 * Real.pi) ^ 2 * ampR A B ϖ 0 0 w +
            ENNReal.ofReal (2 * Real.pi) ^ 2 * ampR A B ϖ 0 m w +
            ENNReal.ofReal (2 * Real.pi) ^ 2 * ampR A B ϖ 1 m w)) := by
        rw [mul_pow]
        refine mul_le_mul' le_rfl ((add3_sq_le _ _ _).trans ?_)
        gcongr
        · exact hT 0 0 (Nat.zero_le m)
        · exact hT 0 m le_rfl
        · exact hT 1 m le_rfl
    _ = _ := by ring

end Plancherel

section Aggregate

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

omit [Fintype ι] in
theorem continuous_iterate_monomial {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} {X : Vec 2 → F} (hX : ContDiff ℝ m X) (i : Fin 2) {j : ℕ} (hj : j ≤ m) {a : ℕ}
    (w : DerivativeWord2 a) :
    Continuous ((dirDeriv i)^[j] fun θ => wordMonomial w θ • X θ) :=
  (contDiff_iterate_dirDeriv (n := m - j) i (j := j) (by
    rw [Nat.sub_add_cancel hj]
    exact ((wordMonomial_contDiff w).of_le (by exact_mod_cast le_top)).smul hX)).continuous

/-- **The inverse-mass sum of the amplitude terms** as one `θ`-integral, bounded by the
amplitude jet norm. -/
theorem sum_lintegral_amp_le (π : ι → ℝ) {m : ℕ} {ϖ : ℝ} (hϖ : 0 < ϖ)
    {A B : ∀ x, Vec 2 → h x} (hA : ∀ x, ContDiff ℝ m (A x)) (hB : ∀ x, ContDiff ℝ m (B x))
    (i : Fin 2) {j : ℕ} (hj : j ≤ m) {a : ℕ} (w : DerivativeWord2 a) :
    ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∫⁻ θ,
        (ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • A x θ) θ‖) ^ 2 +
          ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • B x θ) θ‖) ^ 2) ≤
      ∫⁻ θ, (ENNReal.ofReal (ϖ ^ a * (2 ^ j * ((a : ℝ) + 1) ^ a * (1 + ‖θ‖ / ϖ) ^ a) *
        ((j + 1 : ℕ) * (m.factorial : ℝ))) * amplitudeJetNorm π m ϖ A B θ) ^ 2 := by
  have hm : ∀ x, Measurable fun θ =>
      ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j] (fun θ => wordMonomial w θ • A x θ) θ‖) ^ 2 +
        ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
          (fun θ => wordMonomial w θ • B x θ) θ‖) ^ 2 := fun x =>
    ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_ofReal.comp (continuous_const.mul
      (continuous_iterate_monomial (hA x) i hj w).norm))).measurable.add
    ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_ofReal.comp (continuous_const.mul
      (continuous_iterate_monomial (hB x) i hj w).norm))).measurable
  rw [show (∑ x, ENNReal.ofReal ((π x)⁻¹) * ∫⁻ θ,
        (ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • A x θ) θ‖) ^ 2 +
          ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • B x θ) θ‖) ^ 2)) =
      ∫⁻ θ, ∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • A x θ) θ‖) ^ 2 +
          ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • B x θ) θ‖) ^ 2) by
    rw [lintegral_finsetSum _ fun x _ => (hm x).const_mul _]
    exact Finset.sum_congr rfl fun x _ => (lintegral_const_mul _ (hm x)).symm]
  refine lintegral_mono fun θ => ?_
  have hb := weightedAmp_le_amplitudeJetNorm π hϖ hA hB i hj w θ
  calc ∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • A x θ) θ‖) ^ 2 +
          ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • B x θ) θ‖) ^ 2)
      = ((∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • A x θ) θ‖) ^ 2 +
          ENNReal.ofReal (ϖ ^ j * ‖(dirDeriv i)^[j]
            (fun θ => wordMonomial w θ • B x θ) θ‖) ^ 2)) ^ (1 / 2 : ℝ)) ^ 2 :=
        (rpow_half_sq _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hb 2

end Aggregate

/-- The weighted jet layer of order `a` as a sum over derivative words. -/
theorem eLpNorm_weightedLayer_sq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ϖ : ℝ) (m : ℕ) {a : ℕ} (J : DerivativeWord2 a → Vec 2 → F) (hJ : ∀ w, Continuous (J w)) :
    eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) *
        Real.sqrt (∑ w, ‖J w z‖ ^ 2)) 2 volume ^ 2 =
      ∑ w, eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) • J w z) 2
        volume ^ 2 := by
  have hW := polyWeight_continuous ϖ m
  have hc : ∀ w, Continuous fun z =>
      (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) • J w z := fun w => hW.smul (hJ w)
  have hF : Continuous fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) *
      Real.sqrt (∑ w, ‖J w z‖ ^ 2) :=
    hW.mul (Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => (hJ w).norm.pow 2))
  rw [eLpNorm_two_sq hF.aestronglyMeasurable]
  simp_rw [eLpNorm_two_sq (hc _).aestronglyMeasurable]
  rw [← lintegral_finsetSum (f := fun w z =>
    ‖(1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) • J w z‖ₑ ^ 2) _
    fun w _ => ((ENNReal.continuous_pow 2).comp (hc w).enorm).measurable]
  refine lintegral_congr fun z => ?_
  have hS : 0 ≤ ∑ w, ‖J w z‖ ^ 2 := Finset.sum_nonneg fun w _ => sq_nonneg _
  rw [AVRegularity.CycleWords.Assembly.enorm_sq_eq_ofReal, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hS, Finset.mul_sum,
    ENNReal.ofReal_sum_of_nonneg fun w _ => by positivity]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [AVRegularity.CycleWords.Assembly.enorm_sq_eq_ofReal, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The constant of the weighted jet bound. -/
noncomputable def gaussJetConst (m M : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (M + 1), 3 ^ m * (2 * Real.pi) * Real.sqrt (9 * 2 ^ a) *
    (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)))

theorem gaussJetConst_pos (m M : ℕ) : 0 < gaussJetConst m M := by
  unfold gaussJetConst
  refine Finset.sum_pos (fun a _ => ?_) ⟨0, by simp⟩
  have : 0 < Real.sqrt (9 * 2 ^ a) := Real.sqrt_pos.2 (by positivity)
  positivity

section JetIntegral

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The `θ`-integral of the weighted amplitude jet norm. -/
noncomputable def ampJetIntegral (π : ι → ℝ) (m M : ℕ) (ϖ : ℝ) (A B : ∀ x, Vec 2 → h x) :
    ℝ≥0∞ :=
  ∫⁻ θ, (ENNReal.ofReal ((1 + ‖θ‖ / ϖ) ^ M) * amplitudeJetNorm π m ϖ A B θ) ^ 2

end JetIntegral

section Families

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem sum_ampR_le (π : ι → ℝ) {r : ℝ} {m M : ℕ} {ϖ : ℝ} (hϖ : 0 < ϖ)
    {A B : ∀ x, Vec 2 → h x} (hA : ∀ x, IsBandAmp r m (A x)) (hB : ∀ x, IsBandAmp r m (B x))
    (i : Fin 2) {j : ℕ} (hj : j ≤ m) {a : ℕ} (ha : a ≤ M) (w : DerivativeWord2 a) :
    ∑ x, ENNReal.ofReal ((π x)⁻¹) * ampR (A x) (B x) ϖ i j w ≤
      ENNReal.ofReal (ϖ ^ a * (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) *
        (m.factorial : ℝ)))) ^ 2 * ampJetIntegral π m M ϖ A B := by
  refine (sum_lintegral_amp_le π hϖ (fun x => (hA x).1) (fun x => (hB x).1) i hj w).trans ?_
  unfold ampJetIntegral
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun θ => ?_
  rw [← mul_pow]
  have hQ : 0 ≤ ϖ ^ a * (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) *
      (m.factorial : ℝ))) := by positivity
  rw [show ENNReal.ofReal (ϖ ^ a * (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) *
      (m.factorial : ℝ)))) * (ENNReal.ofReal ((1 + ‖θ‖ / ϖ) ^ M) * amplitudeJetNorm π m ϖ A B θ) =
      ENNReal.ofReal (ϖ ^ a * (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) *
        (m.factorial : ℝ))) * (1 + ‖θ‖ / ϖ) ^ M) * amplitudeJetNorm π m ϖ A B θ by
    rw [ENNReal.ofReal_mul hQ]
    ring]
  refine pow_le_pow_left₀ (by positivity) (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) 2
  have hx : 1 ≤ 1 + ‖θ‖ / ϖ := by
    have := div_nonneg (norm_nonneg θ) hϖ.le
    linarith
  have h1 : (2 : ℝ) ^ j ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hj
  have h2 : (1 + ‖θ‖ / ϖ) ^ a ≤ (1 + ‖θ‖ / ϖ) ^ M := pow_le_pow_right₀ hx ha
  have h3 : ((j + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj
  have hpos : 0 ≤ (1 + ‖θ‖ / ϖ) ^ a := by positivity
  calc ϖ ^ a * (2 ^ j * ((a : ℝ) + 1) ^ a * (1 + ‖θ‖ / ϖ) ^ a) *
        (((j + 1 : ℕ) : ℝ) * (m.factorial : ℝ))
      ≤ ϖ ^ a * (2 ^ m * ((a : ℝ) + 1) ^ a * (1 + ‖θ‖ / ϖ) ^ M) *
        (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)) := by gcongr
    _ = ϖ ^ a * (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ))) *
        (1 + ‖θ‖ / ϖ) ^ M := by ring

theorem layer_sq_le (π : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) {m M : ℕ} {ϖ : ℝ} (hϖ : 0 < ϖ)
    {A B : ∀ x, Vec 2 → h x} (hA : ∀ x, IsBandAmp r m (A x)) (hB : ∀ x, IsBandAmp r m (B x))
    {a : ℕ} (ha : a ≤ M) :
    ∑ x, ENNReal.ofReal ((π x)⁻¹) * eLpNorm (fun z =>
        (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) *
          Real.sqrt (∑ w : DerivativeWord2 a,
            ‖orderedDerivative w (ampFun r (A x) (B x)) z‖ ^ 2)) 2 volume ^ 2 ≤
      ENNReal.ofReal ((3 ^ m) ^ 2 * 3 * (2 * Real.pi) ^ 2 * (2 ^ a * 3) *
        (ϖ ^ a * (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)))) ^ 2) *
        ampJetIntegral π m M ϖ A B := by
  set c : ℝ := 2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)) with hc
  have hc0 : 0 ≤ c := by positivity
  set K₁ : ℝ≥0∞ := ENNReal.ofReal (3 ^ m) ^ 2 * 3 * ENNReal.ofReal (2 * Real.pi) ^ 2 with hK₁
  set I := ampJetIntegral π m M ϖ A B with hI
  have hlayer : ∀ x, eLpNorm (fun z =>
      (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) *
        Real.sqrt (∑ w : DerivativeWord2 a,
          ‖orderedDerivative w (ampFun r (A x) (B x)) z‖ ^ 2)) 2 volume ^ 2 ≤
      ∑ w : DerivativeWord2 a, K₁ * (ampR (A x) (B x) ϖ 0 0 w + ampR (A x) (B x) ϖ 0 m w +
        ampR (A x) (B x) ϖ 1 m w) := fun x => by
    rw [eLpNorm_weightedLayer_sq ϖ m _ fun w =>
      continuous_orderedDerivative_ampFun hr (hA x) (hB x) w]
    exact Finset.sum_le_sum fun w _ => wordTerm_sq_le hr (hA x) (hB x) hϖ.le w
  have hS := fun (i : Fin 2) (j : ℕ) (hj : j ≤ m) (w : DerivativeWord2 a) =>
    sum_ampR_le π hϖ hA hB i hj ha w
  calc ∑ x, ENNReal.ofReal ((π x)⁻¹) * eLpNorm (fun z =>
        (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) *
          Real.sqrt (∑ w : DerivativeWord2 a,
            ‖orderedDerivative w (ampFun r (A x) (B x)) z‖ ^ 2)) 2 volume ^ 2
      ≤ ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∑ w : DerivativeWord2 a,
          K₁ * (ampR (A x) (B x) ϖ 0 0 w + ampR (A x) (B x) ϖ 0 m w +
            ampR (A x) (B x) ϖ 1 m w) := by
        gcongr with x
        exact hlayer x
    _ = K₁ * ∑ w : DerivativeWord2 a,
          ((∑ x, ENNReal.ofReal ((π x)⁻¹) * ampR (A x) (B x) ϖ 0 0 w) +
            (∑ x, ENNReal.ofReal ((π x)⁻¹) * ampR (A x) (B x) ϖ 0 m w) +
            (∑ x, ENNReal.ofReal ((π x)⁻¹) * ampR (A x) (B x) ϖ 1 m w)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ K₁ * ∑ _w : DerivativeWord2 a, 3 * (ENNReal.ofReal (ϖ ^ a * c) ^ 2 * I) := by
        gcongr with w
        calc (∑ x, ENNReal.ofReal ((π x)⁻¹) * ampR (A x) (B x) ϖ 0 0 w) +
              (∑ x, ENNReal.ofReal ((π x)⁻¹) * ampR (A x) (B x) ϖ 0 m w) +
              (∑ x, ENNReal.ofReal ((π x)⁻¹) * ampR (A x) (B x) ϖ 1 m w)
            ≤ ENNReal.ofReal (ϖ ^ a * c) ^ 2 * I + ENNReal.ofReal (ϖ ^ a * c) ^ 2 * I +
                ENNReal.ofReal (ϖ ^ a * c) ^ 2 * I := by
              gcongr
              · exact hS 0 0 (Nat.zero_le m) w
              · exact hS 0 m le_rfl w
              · exact hS 1 m le_rfl w
          _ = 3 * (ENNReal.ofReal (ϖ ^ a * c) ^ 2 * I) := by ring
    _ = _ := by
        have eZ : ENNReal.ofReal ((3 ^ m) ^ 2 * 3 * (2 * Real.pi) ^ 2 * (2 ^ a * 3) *
            (ϖ ^ a * c) ^ 2) = ENNReal.ofReal (3 ^ m) ^ 2 * 3 * ENNReal.ofReal (2 * Real.pi) ^ 2 *
              (2 ^ a * 3) * ENNReal.ofReal (ϖ ^ a * c) ^ 2 := by
          rw [ENNReal.ofReal_mul (by positivity :
              (0 : ℝ) ≤ (3 ^ m) ^ 2 * 3 * (2 * Real.pi) ^ 2 * (2 ^ a * 3)),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (3 ^ m) ^ 2 * 3 * (2 * Real.pi) ^ 2),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (3 ^ m) ^ 2 * 3),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (3 ^ m) ^ 2),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ a),
            ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 3 ^ m),
            ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
            ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ϖ ^ a * c),
            ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_ofNat]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, hK₁, eZ]
        push_cast
        ring

/-- **Weighted jets of a band-limited family** by the `θ`-integral of its amplitude jet norm. -/
theorem weightedJetNorm_ampFun_le (π : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) {m M : ℕ} {ϖ : ℝ}
    (hϖ : 0 < ϖ) {A B : ∀ x, Vec 2 → h x} (hA : ∀ x, IsBandAmp r m (A x))
    (hB : ∀ x, IsBandAmp r m (B x)) :
    weightedJetNorm π (m : ℝ) M ϖ ϖ⁻¹
        (fun x _ wd z => orderedDerivative wd (ampFun r (A x) (B x)) z) ≤
      ENNReal.ofReal (gaussJetConst m M) * ampJetIntegral π m M ϖ A B ^ (1 / 2 : ℝ) := by
  unfold weightedJetNorm gaussJetConst
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by
    have : 0 ≤ Real.sqrt (9 * 2 ^ a) := Real.sqrt_nonneg _
    positivity), Finset.sum_mul]
  refine Finset.sum_le_sum fun a ha => ?_
  have haM : a ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
  set C : ℝ := 3 ^ m * (2 * Real.pi) * Real.sqrt (9 * 2 ^ a) *
    (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ))) with hC
  have hC0 : 0 ≤ C := by
    have : 0 ≤ Real.sqrt (9 * 2 ^ a) := Real.sqrt_nonneg _
    positivity
  have hL := layer_sq_le π hr hϖ hA hB haM
  have hroot := ENNReal.rpow_le_rpow hL (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hZ : (3 ^ m) ^ 2 * 3 * (2 * Real.pi) ^ 2 * (2 ^ a * 3) *
      (ϖ ^ a * (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)))) ^ 2 =
      (C * ϖ ^ a) ^ 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 9 * 2 ^ a by positivity)
    calc (3 ^ m) ^ 2 * 3 * (2 * Real.pi) ^ 2 * (2 ^ a * 3) *
          (ϖ ^ a * (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)))) ^ 2
        = (3 ^ m * (2 * Real.pi) * (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) *
            (m.factorial : ℝ))) * ϖ ^ a) ^ 2 * (9 * 2 ^ a) := by ring
      _ = (3 ^ m * (2 * Real.pi) * (2 ^ m * ((a : ℝ) + 1) ^ a * (((m + 1 : ℕ) : ℝ) *
            (m.factorial : ℝ))) * ϖ ^ a) ^ 2 * Real.sqrt (9 * 2 ^ a) ^ 2 := by rw [hs]
      _ = (C * ϖ ^ a) ^ 2 := by rw [hC]; ring
  rw [hZ, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_pow (by positivity),
    sq_rpow_half] at hroot
  have hfac0 : 1 ≤ a.factorial := Nat.factorial_pos a
  have hfac : (1 : ℝ) ≤ a.factorial := by exact_mod_cast hfac0
  calc ENNReal.ofReal (ϖ⁻¹ ^ a / (a.factorial : ℝ)) * (∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((m : ℝ) / 2) *
          Real.sqrt (∑ w : DerivativeWord2 a,
            ‖orderedDerivative w (ampFun r (A v) (B v)) z‖ ^ 2)) 2 volume ^ 2) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (ϖ⁻¹ ^ a) * (ENNReal.ofReal (C * ϖ ^ a) *
          ampJetIntegral π m M ϖ A B ^ (1 / 2 : ℝ)) := by
        gcongr
        exact div_le_self (by positivity) hfac
    _ = ENNReal.ofReal C * ampJetIntegral π m M ϖ A B ^ (1 / 2 : ℝ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [inv_pow, mul_comm C, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero a hϖ.ne'), one_mul]

end Families

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization Filter AVRegularity.Sobolev
open scoped ENNReal Topology
namespace AVRegularity.CycleWords.Assembly

/-! # Absorbing the Gaussian factor

`(1 + x)^q e^{-c x²}` is bounded for `x ≥ 0` (`gauss_absorb`). The amplitude jet norm vanishes
outside the frequency cube when the amplitudes vanish for `|θ| ≥ π/2` (`amplitudeJetNorm_eq_zero`),
so a Gaussian amplitude bound on the cube bounds the integral of the weighted amplitude jet norm
by the cube integral of the Bloch fibre norms (`ampJetIntegral_le_cube`). -/

/-- The constant of `(1 + x)^q e^{-c x²} ≤ K`. -/
noncomputable def gaussConst (q : ℕ) (c : ℝ) : ℝ := 2 ^ q * (2 + (q.factorial : ℝ) / c ^ q)

theorem gaussConst_pos (q : ℕ) {c : ℝ} (hc : 0 < c) : 0 < gaussConst q c := by
  unfold gaussConst
  positivity

/-- **Gaussian absorption.** -/
theorem gauss_absorb (q : ℕ) {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ q * Real.exp (-c * x ^ 2) ≤ gaussConst q c := by
  have he : 0 < Real.exp (-c * x ^ 2) := Real.exp_pos _
  have he1 : Real.exp (-c * x ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  -- `(1 + x)^q ≤ 2^q (1 + x^q)` and `x^q ≤ 1 + x^{2q}`
  have h1 : (1 + x) ^ q ≤ 2 ^ q * (1 + x ^ q) := by
    rcases le_total x 1 with hx1 | hx1
    · calc (1 + x) ^ q ≤ 2 ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
        _ ≤ 2 ^ q * (1 + x ^ q) := le_mul_of_one_le_right (by positivity)
            (by linarith [pow_nonneg hx q])
    · calc (1 + x) ^ q ≤ (2 * x) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
        _ = 2 ^ q * x ^ q := mul_pow _ _ _
        _ ≤ 2 ^ q * (1 + x ^ q) := by gcongr; linarith
  have h2 : x ^ q ≤ 1 + x ^ (2 * q) := by
    rcases le_total x 1 with hx1 | hx1
    · have := pow_le_one₀ hx hx1 (n := q)
      linarith [pow_nonneg hx (2 * q)]
    · have : x ^ q ≤ x ^ (2 * q) := pow_le_pow_right₀ hx1 (by omega)
      linarith
  -- `x^{2q} e^{-c x²} ≤ q!/c^q`
  have h3 : x ^ (2 * q) * Real.exp (-c * x ^ 2) ≤ (q.factorial : ℝ) / c ^ q := by
    have hq := Real.pow_div_factorial_le_exp (x := c * x ^ 2) (by positivity) q
    have hfac : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
    have hcq : 0 < c ^ q := pow_pos hc q
    rw [div_le_iff₀ hfac] at hq
    have hx2 : x ^ (2 * q) = (c * x ^ 2) ^ q / c ^ q := by
      rw [mul_pow, ← pow_mul, mul_comm 2 q]
      field_simp
    rw [hx2, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hcq]
    calc (c * x ^ 2) ^ q * Real.exp (-c * x ^ 2)
        ≤ Real.exp (c * x ^ 2) * q.factorial * Real.exp (-c * x ^ 2) :=
          mul_le_mul_of_nonneg_right hq he.le
      _ = q.factorial := by
          rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
          simp
  calc (1 + x) ^ q * Real.exp (-c * x ^ 2)
      ≤ 2 ^ q * (2 + x ^ (2 * q)) * Real.exp (-c * x ^ 2) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    _ = 2 ^ q * (2 * Real.exp (-c * x ^ 2) + x ^ (2 * q) * Real.exp (-c * x ^ 2)) := by ring
    _ ≤ 2 ^ q * (2 * 1 + (q.factorial : ℝ) / c ^ q) := by gcongr
    _ = gaussConst q c := by rw [gaussConst]; ring

theorem norm_le_sqrt_vecDot (θ : Vec 2) : ‖θ‖ ≤ Real.sqrt (vecDot θ θ) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => θ j * θ j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

/-- The frequency cube `|θ_i| ≤ π`. -/
def freqCube : Set (Vec 2) := {θ | ∀ i, |θ i| ≤ Real.pi}

theorem measurableSet_freqCube : MeasurableSet freqCube := by
  have : freqCube = ⋂ i, {θ : Vec 2 | |θ i| ≤ Real.pi} := by
    ext θ
    simp [freqCube]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const

section Vanish

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- Outside the frequency cube the amplitude jet norm vanishes. -/
theorem amplitudeJetNorm_eq_zero (π : ι → ℝ) (m : ℕ) (ϖ : ℝ) {A B : ∀ x, Vec 2 → h x}
    (hvan : ∀ x θ, Real.pi / 2 ≤ Real.sqrt (vecDot θ θ) → A x θ = 0 ∧ B x θ = 0)
    {θ : Vec 2} (hθ : θ ∉ freqCube) : amplitudeJetNorm π m ϖ A B θ = 0 := by
  have hbig : Real.pi / 2 < Real.sqrt (vecDot θ θ) := by
    have hθ' : ¬ ∀ i, |θ i| ≤ Real.pi := hθ
    push Not at hθ'
    obtain ⟨i, hi⟩ := hθ'
    have := norm_le_sqrt_vecDot θ
    have hi' : |θ i| ≤ ‖θ‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm θ i
    linarith [Real.pi_pos]
  have hopen : IsOpen {θ : Vec 2 | Real.pi / 2 < Real.sqrt (vecDot θ θ)} :=
    isOpen_lt continuous_const (Real.continuous_sqrt.comp (by unfold vecDot; fun_prop))
  have hev : ∀ x, (A x =ᶠ[𝓝 θ] fun _ => 0) ∧ (B x =ᶠ[𝓝 θ] fun _ => 0) := fun x =>
    ⟨eventually_of_mem (hopen.mem_nhds hbig) fun y hy => (hvan x y hy.le).1,
      eventually_of_mem (hopen.mem_nhds hbig) fun y hy => (hvan x y hy.le).2⟩
  have hz : ∀ x (a b : ℕ), thetaPartial a b (A x) θ = 0 ∧ thetaPartial a b (B x) θ = 0 := by
    intro x a b
    unfold thetaPartial
    rw [((hev x).1.iteratedFDeriv ℝ (a + b)).eq_of_nhds,
      ((hev x).2.iteratedFDeriv ℝ (a + b)).eq_of_nhds]
    simp
  unfold amplitudeJetNorm
  refine Finset.sum_eq_zero fun β _ => ?_
  simp [hz, ENNReal.zero_rpow_of_pos]

/-- **The amplitude integral by the cube integral** of the Gaussian majorant. -/
theorem ampJetIntegral_le_cube (π : ι → ℝ) {m M p : ℕ} {ϖ : ℝ} (hϖ : 0 < ϖ) {cGa CGa : ℝ}
    (hc : 0 < cGa) (hC : 0 ≤ CGa) {A B : ∀ x, Vec 2 → h x}
    (hvan : ∀ x θ, Real.pi / 2 ≤ Real.sqrt (vecDot θ θ) → A x θ = 0 ∧ B x θ = 0)
    (Φ : Vec 2 → ℝ≥0∞)
    (hgauss : ∀ θ ∈ freqCube, amplitudeJetNorm π m ϖ A B θ ≤
      ENNReal.ofReal (CGa * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ p *
        Real.exp (-cGa * (vecDot θ θ / ϖ ^ 2))) * Φ θ) :
    ampJetIntegral π m M ϖ A B ≤
      ENNReal.ofReal (CGa * gaussConst (M + p) cGa) ^ 2 * ∫⁻ θ in freqCube, Φ θ ^ 2 := by
  unfold ampJetIntegral
  have hsupp : Function.support (fun θ =>
      (ENNReal.ofReal ((1 + ‖θ‖ / ϖ) ^ M) * amplitudeJetNorm π m ϖ A B θ) ^ 2) ⊆ freqCube := by
    intro θ hθ
    by_contra hθc
    exact hθ (by simp [amplitudeJetNorm_eq_zero π m ϖ hvan hθc])
  rw [← setLIntegral_eq_of_support_subset hsupp, ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_freqCube fun θ hθ => ?_)
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  set ρ := Real.sqrt (vecDot θ θ) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hx0 : 0 ≤ ρ / ϖ := div_nonneg hρ0 hϖ.le
  have hvd : vecDot θ θ / ϖ ^ 2 = (ρ / ϖ) ^ 2 := by
    have hv : 0 ≤ vecDot θ θ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rw [div_pow, hρ, Real.sq_sqrt hv]
  have hn : (1 + ‖θ‖ / ϖ) ^ M ≤ (1 + ρ / ϖ) ^ M := by
    gcongr
    exact norm_le_sqrt_vecDot θ
  have hK := gauss_absorb (M + p) hc hx0
  calc ENNReal.ofReal ((1 + ‖θ‖ / ϖ) ^ M) * amplitudeJetNorm π m ϖ A B θ
      ≤ ENNReal.ofReal ((1 + ρ / ϖ) ^ M) * (ENNReal.ofReal (CGa * (1 + ρ / ϖ) ^ p *
          Real.exp (-cGa * (ρ / ϖ) ^ 2)) * Φ θ) := by
        rw [← hvd]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hn) (hgauss θ hθ)
    _ = ENNReal.ofReal (CGa * ((1 + ρ / ϖ) ^ (M + p) * Real.exp (-cGa * (ρ / ϖ) ^ 2))) *
          Φ θ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
    _ ≤ ENNReal.ofReal (CGa * gaussConst (M + p) cGa) * Φ θ := by
        gcongr

end Vanish

end AVRegularity.CycleWords.Assembly
end
