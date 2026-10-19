-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.TransformBoundCLM
import AVRegularity.CycleWords.MixedWords.ConstituentTransposeStep

/-! # the term operators of the letter transform

`twIter θ k K m : H^{K+m} → H^K` is `(∂_k + iθ_k)^m` (a chain of `tbTwist`), `powOp` the twisted
power `D_0^p D_1^q`, and `unitOp` the composite with the multiplier by a real coefficient `c`.
`Realizes N n G B` says that `G` (a functional of the classical representative of the argument) is
the value of a real-linear map `H^N → H^n` of norm `≤ B`; the class is closed under sums and real
multiples.  `realizes_unit0` and `realizes_unit1` realize the unit terms
`κ D_θ^{(p,q)}(c f)` and `κ D_θ^{(p,q)}(c D_{θ,k} f)`; `star_fibreCovPow` conjugates the transforms
at `-θ` of the conjugate test. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
  AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Variational

namespace AVRegularity.CycleWords.Assembly

section Chain

/-- The chain `(∂_k + iθ_k)^m : H^{K+m} → H^K`. -/
def twIter (θ : Vec 2) (k : Fin 2) (K : ℕ) : ∀ m : ℕ, TorusHk (K + m) ℂ →L[ℝ] TorusHk K ℂ
  | 0 => ContinuousLinearMap.id ℝ _
  | m + 1 => (twIter θ k K m).comp (tbTwist (K + m) θ k)

theorem twIter_norm (θ : Vec 2) (k : Fin 2) (K : ℕ) :
    ∀ (m : ℕ) (U : TorusHk (K + m) ℂ), ‖twIter θ k K m U‖ ≤ (1 + |θ k|) ^ m * ‖U‖
  | 0, U => by simp [twIter]
  | m + 1, U => by
    have h1 := twIter_norm θ k K m (tbTwist (K + m) θ k U)
    have h2 : ‖tbTwist (K + m) θ k U‖ ≤ (1 + |θ k|) * ‖U‖ :=
      ((tbTwist (K + m) θ k).le_opNorm U).trans
        (mul_le_mul_of_nonneg_right (tbTwist_norm_le _ θ k) (norm_nonneg _))
    calc ‖twIter θ k K (m + 1) U‖ = ‖twIter θ k K m (tbTwist (K + m) θ k U)‖ := rfl
      _ ≤ (1 + |θ k|) ^ m * ‖tbTwist (K + m) θ k U‖ := h1
      _ ≤ (1 + |θ k|) ^ m * ((1 + |θ k|) * ‖U‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 + |θ k|) ^ (m + 1) * ‖U‖ := by ring

theorem twIter_value (θ : Vec 2) (k : Fin 2) (K : ℕ) :
    ∀ (m : ℕ) (U : TorusHk (K + m) ℂ) (f : Vec 2 → ℂ), ContDiff ℝ m f →
      (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f →
      (torusHkValueCLM (twIter θ k K m U) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
        (fibreCovDeriv θ k)^[m] f
  | 0, U, f, _, hv => by simpa [twIter] using hv
  | m + 1, U, f, hf, hv => by
    have h1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.le_add_left 1 m)
    have h2 := tbTwist_value_ae (K + m) θ k U f h1 hv
    have h3 : ContDiff ℝ m (fibreCovDeriv θ k f) := contDiff_fibreCovDeriv (j := m) hf θ k
    have h4 := twIter_value θ k K m (tbTwist (K + m) θ k U) _ h3 h2
    rw [Function.iterate_succ_apply]
    exact h4

/-- The twisted power `D_0^p D_1^q : H^{n+p+q} → H^n`. -/
def powOp (θ : Vec 2) (n p q : ℕ) : TorusHk (n + p + q) ℂ →L[ℝ] TorusHk n ℂ :=
  (twIter θ 0 n p).comp (twIter θ 1 (n + p) q)

theorem powOp_norm (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n p q : ℕ)
    (U : TorusHk (n + p + q) ℂ) : ‖powOp θ n p q U‖ ≤ (1 + ρ) ^ (p + q) * ‖U‖ := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  have h1 := twIter_norm θ 1 (n + p) q U
  have h2 := twIter_norm θ 0 n p (twIter θ 1 (n + p) q U)
  have a1 : (1 + |θ 1|) ^ q ≤ (1 + ρ) ^ q := pow_le_pow_left₀ (by positivity) (by linarith [hθ 1]) q
  have a0 : (1 + |θ 0|) ^ p ≤ (1 + ρ) ^ p := pow_le_pow_left₀ (by positivity) (by linarith [hθ 0]) p
  calc ‖powOp θ n p q U‖ = ‖twIter θ 0 n p (twIter θ 1 (n + p) q U)‖ := rfl
    _ ≤ (1 + |θ 0|) ^ p * ‖twIter θ 1 (n + p) q U‖ := h2
    _ ≤ (1 + |θ 0|) ^ p * ((1 + |θ 1|) ^ q * ‖U‖) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (1 + ρ) ^ p * ((1 + ρ) ^ q * ‖U‖) := by gcongr
    _ = (1 + ρ) ^ (p + q) * ‖U‖ := by ring

theorem powOp_value (θ : Vec 2) (n p q : ℕ) (U : TorusHk (n + p + q) ℂ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (p + q : ℕ) f)
    (hv : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f) :
    (torusHkValueCLM (powOp θ n p q U) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fibreCovPow θ (p, q) f := by
  have h1 : ContDiff ℝ q f := hf.of_le (by exact_mod_cast Nat.le_add_left q p)
  have h2 := twIter_value θ 1 (n + p) q U f h1 hv
  have h3 : ContDiff ℝ p ((fibreCovDeriv θ 1)^[q] f) :=
    contDiff_fibreCovDeriv_iterate θ 1 p q hf
  exact twIter_value θ 0 n p _ _ h3 h2

/-- The multiplier by `c` followed by the twisted power. -/
def unitOp (θ : Vec 2) (n p q : ℕ) {c : Vec 2 → ℝ} (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c)
    (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) :
    TorusHk (n + p + q) ℂ →L[ℝ] TorusHk n ℂ :=
  (powOp θ n p q).comp (tbMulCLM (n + p + q) hc hp hP)

end Chain

theorem unitOp_norm (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n p q : ℕ) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (U : TorusHk (n + p + q) ℂ) :
    ‖unitOp θ n p q hc hp hP U‖ ≤
      (1 + ρ) ^ (p + q) * (cellDriftNativePrice (n + p + q) * P) * ‖U‖ := by
  have h1 := powOp_norm θ ρ hθ n p q (tbMulCLM (n + p + q) hc hp hP U)
  have h2 := tbMulCLM_norm_le (n + p + q) hc hp hP U
  calc ‖unitOp θ n p q hc hp hP U‖ = ‖powOp θ n p q (tbMulCLM (n + p + q) hc hp hP U)‖ := rfl
    _ ≤ (1 + ρ) ^ (p + q) * ‖tbMulCLM (n + p + q) hc hp hP U‖ := h1
    _ ≤ (1 + ρ) ^ (p + q) * (cellDriftNativePrice (n + p + q) * P * ‖U‖) :=
        mul_le_mul_of_nonneg_left h2 (by
          have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
          positivity)
    _ = _ := by ring

theorem unitOp_value (θ : Vec 2) (n p q : ℕ) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (U : TorusHk (n + p + q) ℂ)
    (g : Vec 2 → ℂ) (hg : ContDiff ℝ (p + q : ℕ) (fun x => (c x : ℂ) * g x))
    (hv : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] g) :
    (torusHkValueCLM (unitOp θ n p q hc hp hP U) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube]
        fibreCovPow θ (p, q) (fun x => (c x : ℂ) * g x) := by
  have h1 := tbMulCLM_value_ae (n + p + q) hc hp hP U
  have h2 : (torusHkValueCLM (tbMulCLM (n + p + q) hc hp hP U) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => (c x : ℂ) * g x := by
    filter_upwards [h1, hv] with x e1 e2
    rw [e1, e2]
  exact powOp_value θ n p q _ _ hg h2

section Conj

theorem fibreCovDeriv_star (θ : Vec 2) (k : Fin 2) {f : Vec 2 → ℂ} (hf : Differentiable ℝ f) :
    fibreCovDeriv (-θ) k (fun y => star (f y)) = fun z => star (fibreCovDeriv θ k f z) := by
  funext z
  have := tb_star_cov θ k f z (hf z)
  rw [← this, star_star]

theorem fibreCovDeriv_iter_star (θ : Vec 2) (k : Fin 2) :
    ∀ (m : ℕ) {f : Vec 2 → ℂ}, ContDiff ℝ m f →
      (fibreCovDeriv (-θ) k)^[m] (fun y => star (f y)) =
        fun z => star ((fibreCovDeriv θ k)^[m] f z)
  | 0, _, _ => rfl
  | m + 1, f, hf => by
    have h1 : Differentiable ℝ f := (hf.of_le (by exact_mod_cast Nat.le_add_left 1 m)).differentiable
      one_ne_zero
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, fibreCovDeriv_star θ k h1]
    have h2 : ContDiff ℝ m (fibreCovDeriv θ k f) := contDiff_fibreCovDeriv (j := m) hf θ k
    exact fibreCovDeriv_iter_star θ k m h2

/-- The transform at `-θ` of the conjugate is the conjugate of the transform at `θ`. -/
theorem star_fibreCovPow (θ : Vec 2) (b : ℕ × ℕ) {f : Vec 2 → ℂ}
    (hf : ContDiff ℝ (b.1 + b.2 : ℕ) f) (z : Vec 2) :
    star (fibreCovPow (-θ) b (fun y => star (f y)) z) = fibreCovPow θ b f z := by
  unfold fibreCovPow
  have h1 : ContDiff ℝ b.2 f := hf.of_le (by exact_mod_cast Nat.le_add_left b.2 b.1)
  have h2 := fibreCovDeriv_iter_star θ 1 b.2 h1
  have h3 : ContDiff ℝ b.1 ((fibreCovDeriv θ 1)^[b.2] f) :=
    contDiff_fibreCovDeriv_iterate θ 1 b.1 b.2 hf
  rw [h2, fibreCovDeriv_iter_star θ 0 b.1 h3]
  simp

end Conj



section Realizes

/-- A real multiple of a real-linear map (with the expected type spelled out). -/
def lrSmul {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (a : ℝ) (A : X →L[ℝ] Y) : X →L[ℝ] Y := a • A

theorem lrSmul_apply {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (a : ℝ) (A : X →L[ℝ] Y) (x : X) : lrSmul a A x = a • A x := rfl

/-- `G`, a functional of the classical representative of the argument, is realized by a real-linear
map `H^N → H^n` of norm `≤ B`. -/
def Realizes (N n : ℕ) (G : (Vec 2 → ℂ) → Vec 2 → ℂ) (B : ℝ) : Prop :=
  ∃ A : TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ ψ, (torusHkValueCLM (A ψ) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      G (torusHigherClassicalValue N ψ)) ∧ ∀ ψ, ‖A ψ‖ ≤ B * ‖ψ‖

variable {N n : ℕ} {G G' : (Vec 2 → ℂ) → Vec 2 → ℂ} {B B' : ℝ}

theorem Realizes.zero : Realizes N n (fun _ _ => 0) 0 :=
  ⟨0, fun ψ => by
    rw [zero_apply, map_zero]
    exact Lp.coeFn_zero _ _ _, fun ψ => by simp⟩

theorem Realizes.mono (h : Realizes N n G B) (hB : B ≤ B') : Realizes N n G B' := by
  obtain ⟨A, hv, hn⟩ := h
  exact ⟨A, hv, fun ψ => (hn ψ).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))⟩

theorem Realizes.congr (h : Realizes N n G B)
    (hG : ∀ ψ : TorusHk N ℂ, G (torusHigherClassicalValue N ψ) =
      G' (torusHigherClassicalValue N ψ)) : Realizes N n G' B := by
  obtain ⟨A, hv, hn⟩ := h
  exact ⟨A, fun ψ => by rw [← hG ψ]; exact hv ψ, hn⟩

theorem Realizes.add (h : Realizes N n G B) (h' : Realizes N n G' B') :
    Realizes N n (fun f z => G f z + G' f z) (B + B') := by
  obtain ⟨A, hv, hn⟩ := h
  obtain ⟨A', hv', hn'⟩ := h'
  refine ⟨A + A', fun ψ => ?_, fun ψ => ?_⟩
  · rw [add_apply, map_add]
    filter_upwards [Lp.coeFn_add (torusHkValueCLM (A ψ)) (torusHkValueCLM (A' ψ)), hv ψ, hv' ψ]
      with z h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
  · rw [add_apply]
    exact (norm_add_le _ _).trans (by nlinarith [hn ψ, hn' ψ])

theorem Realizes.smul (h : Realizes N n G B) (a : ℝ) :
    Realizes N n (fun f z => (a : ℂ) * G f z) (|a| * B) := by
  obtain ⟨A, hv, hn⟩ := h
  refine ⟨lrSmul a A, fun ψ => ?_, fun ψ => ?_⟩
  · rw [lrSmul_apply, map_smul]
    filter_upwards [Lp.coeFn_smul a (torusHkValueCLM (A ψ)), hv ψ] with z h1 h2
    rw [h1]
    simp only [Pi.smul_apply, h2, Complex.real_smul]
  · rw [lrSmul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hn ψ) (abs_nonneg _)

theorem Realizes.finset_sum {κ : Type*} (s : Finset κ) {G : κ → (Vec 2 → ℂ) → Vec 2 → ℂ}
    {B : κ → ℝ} (h : ∀ j ∈ s, Realizes N n (G j) (B j)) :
    Realizes N n (fun f z => ∑ j ∈ s, G j f z) (∑ j ∈ s, B j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Realizes.zero (N := N) (n := n))
  | insert a s ha ih =>
    have := (h a (Finset.mem_insert_self a s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert ha] using this

theorem Realizes.list_sum {κ : Type*} (l : List κ) {G : κ → (Vec 2 → ℂ) → Vec 2 → ℂ}
    {B : κ → ℝ} (h : ∀ j ∈ l, Realizes N n (G j) (B j)) :
    Realizes N n (fun f z => (l.map fun j => G j f z).sum) (l.map B).sum := by
  induction l with
  | nil => simpa using (Realizes.zero (N := N) (n := n))
  | cons a l ih =>
    have := (h a List.mem_cons_self).add (ih fun j hj => h j (List.mem_cons_of_mem _ hj))
    simpa using this

end Realizes

section Units

variable {N n : ℕ}

private theorem classical_facts (N p q : ℕ) (h2 : p + q + 3 ≤ N) (ψ : TorusHk N ℂ) :
    ContDiff ℝ ((p + q + 1 : ℕ) : ℕ∞) (torusHigherClassicalValue N ψ) ∧
      (torusHkValueCLM ψ : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
        torusHigherClassicalValue N ψ :=
  ⟨torusHigherClassicalValue_contDiff N (p + q + 1) (by omega) ψ,
    (torusHigherClassicalValue_ae N (by omega) ψ).symm⟩

theorem contDiff_real_mul_complex {c : Vec 2 → ℝ} {f : Vec 2 → ℂ} {m : ℕ}
    (hc : ContDiff ℝ (m : ℕ∞) c) (hf : ContDiff ℝ (m : ℕ∞) f) :
    ContDiff ℝ (m : ℕ∞) (fun x => (c x : ℂ) * f x) :=
  (Complex.ofRealCLM.contDiff.comp hc).mul hf

/-- **Unit term, no extra derivative**: `κ D_θ^{(p,q)}(c f)`. -/
theorem realizes_unit0 (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n N p q : ℕ)
    (h1 : n + p + q ≤ N) (h2 : p + q + 3 ≤ N) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (κ : ℝ) :
    Realizes N n (fun f z => (κ : ℂ) * fibreCovPow θ (p, q) (fun y => (c y : ℂ) * f y) z)
      (|κ| * ((1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P))) := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0 (Nat.zero_le _) 0)
  refine ⟨lrSmul κ ((unitOp θ n p q hc hp hP).comp (truncateTorusHk h1)), fun ψ => ?_,
    fun ψ => ?_⟩
  · obtain ⟨hcd, hae⟩ := classical_facts N p q h2 ψ
    have hv : (torusHkValueCLM (truncateTorusHk h1 ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] torusHigherClassicalValue N ψ := hae
    have hcp : ContDiff ℝ (p + q : ℕ) (fun x => (c x : ℂ) * torusHigherClassicalValue N ψ x) :=
      contDiff_real_mul_complex (hc.of_le (by exact_mod_cast (by omega : p + q ≤ n + p + q)))
        (hcd.of_le (by exact_mod_cast (by omega : p + q ≤ p + q + 1)))
    have := unitOp_value θ n p q hc hp hP (truncateTorusHk h1 ψ) _ hcp hv
    rw [lrSmul_apply, map_smul]
    filter_upwards [Lp.coeFn_smul κ (torusHkValueCLM (unitOp θ n p q hc hp hP
      (truncateTorusHk h1 ψ))), this] with z e1 e2
    rw [ContinuousLinearMap.comp_apply, e1]
    simp only [Pi.smul_apply, e2, Complex.real_smul]
  · rw [lrSmul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h3 := unitOp_norm θ ρ hθ n p q hc hp hP (truncateTorusHk h1 ψ)
    have hn := truncateTorusHk_norm_le h1 ψ
    have hX : 0 ≤ (1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) := by positivity
    have hle : cellDriftNativePrice (n + p + q) * P ≤ |cellDriftNativePrice (n + p + q)| * P :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hP0
    rw [ContinuousLinearMap.comp_apply]
    calc _ ≤ (1 + ρ) ^ (p + q) * (cellDriftNativePrice (n + p + q) * P) *
          ‖truncateTorusHk h1 ψ‖ := h3
      _ ≤ (1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) * ‖ψ‖ := by
          gcongr
      _ = _ := by ring

/-- **Unit term with one extra twisted derivative**: `κ D_θ^{(p,q)}(c D_{θ,k} f)`. -/
theorem realizes_unit1 (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n N p q : ℕ) (k : Fin 2)
    (h1 : n + p + q + 1 ≤ N) (h2 : p + q + 3 ≤ N) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (κ : ℝ) :
    Realizes N n (fun f z => (κ : ℂ) * fibreCovPow θ (p, q)
        (fun y => (c y : ℂ) * fibreCovDeriv θ k f y) z)
      (|κ| * ((1 + ρ) ^ (p + q + 1) * (|cellDriftNativePrice (n + p + q)| * P))) := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0 (Nat.zero_le _) 0)
  refine ⟨lrSmul κ ((unitOp θ n p q hc hp hP).comp
    ((tbTwist (n + p + q) θ k).comp (truncateTorusHk h1))), fun ψ => ?_, fun ψ => ?_⟩
  · obtain ⟨hcd, hae⟩ := classical_facts N p q h2 ψ
    have hv : (torusHkValueCLM (truncateTorusHk h1 ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] torusHigherClassicalValue N ψ := hae
    have hc1 : ContDiff ℝ 1 (torusHigherClassicalValue N ψ) :=
      hcd.of_le (by exact_mod_cast (by omega : 1 ≤ p + q + 1))
    have hD := tbTwist_value_ae (n + p + q) θ k (truncateTorusHk h1 ψ) _ hc1 hv
    have hcd' : ContDiff ℝ (p + q : ℕ) (fibreCovDeriv θ k (torusHigherClassicalValue N ψ)) :=
      contDiff_fibreCovDeriv (j := p + q) hcd θ k
    have hcp : ContDiff ℝ (p + q : ℕ)
        (fun x => (c x : ℂ) * fibreCovDeriv θ k (torusHigherClassicalValue N ψ) x) :=
      contDiff_real_mul_complex (hc.of_le (by exact_mod_cast (by omega : p + q ≤ n + p + q))) hcd'
    have := unitOp_value θ n p q hc hp hP (tbTwist (n + p + q) θ k (truncateTorusHk h1 ψ)) _ hcp hD
    rw [lrSmul_apply, map_smul]
    filter_upwards [Lp.coeFn_smul κ (torusHkValueCLM (unitOp θ n p q hc hp hP
      (tbTwist (n + p + q) θ k (truncateTorusHk h1 ψ)))), this] with z e1 e2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, e1]
    simp only [Pi.smul_apply, e2, Complex.real_smul]
  · rw [lrSmul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h3 := unitOp_norm θ ρ hθ n p q hc hp hP (tbTwist (n + p + q) θ k (truncateTorusHk h1 ψ))
    have h4 : ‖tbTwist (n + p + q) θ k (truncateTorusHk h1 ψ)‖ ≤ (1 + ρ) * ‖ψ‖ :=
      ((tbTwist (n + p + q) θ k).le_opNorm _).trans
        (mul_le_mul ((tbTwist_norm_le _ θ k).trans (by linarith [hθ k]))
          (truncateTorusHk_norm_le h1 ψ) (norm_nonneg _) (by linarith))
    have hle : cellDriftNativePrice (n + p + q) * P ≤ |cellDriftNativePrice (n + p + q)| * P :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hP0
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    calc _ ≤ (1 + ρ) ^ (p + q) * (cellDriftNativePrice (n + p + q) * P) *
          ‖tbTwist (n + p + q) θ k (truncateTorusHk h1 ψ)‖ := h3
      _ ≤ (1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) * ((1 + ρ) * ‖ψ‖) := by
          gcongr
      _ = _ := by ring

end Units

end AVRegularity.CycleWords.Assembly
