-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.ActualMeans.Kernel
public import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.ActualMeans

/-! Jets of the chain-rule coefficients and of the kernel of one pulse at the chart scale.


All bounds are carried in scale-weighted form `Rχ^i ‖D^i f‖ ≤ B` (`ScaledJet`), which is stable
under products (Leibniz), finite sums, constant multiples and composition with a chart whose
jets are normalized at the scale `Rχ` (Faà di Bruno).

* `chainCoeff_scaled_bound`: `‖D^i P_{α,β}‖ ≤ C Rχ^{-(|α| - |β| + i)}`, by induction on `|α|` along
  the recursion `P_{αi,βj} = ∂_i P_{α,βj} + P_{α,β} ∂_iΦ_j`.
* `pulseKernel_jet_bound`: `‖D^j K_{β,k'}‖ ≤ C A ∑_{n ≥ d'} c⁻¹ (ε_c ρ)^n Rχ^{-(n + j - d')}` for
  the kernel of one pulse with letters of size `A λ^{n - d + i}`, `λ = ρ / Rχ`. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Real-number bookkeeping -/

/-- From an unscaled bound to a scale-weighted bound. -/
theorem scaled_le_of_le_inv_pow {s t B : ℝ} (hs : 0 < s) (q : ℕ) (h : t ≤ B * s⁻¹ ^ q) :
    s ^ q * t ≤ B := by
  have h1 : s ^ q * s⁻¹ ^ q = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hs.ne', one_pow]
  calc s ^ q * t ≤ s ^ q * (B * s⁻¹ ^ q) := mul_le_mul_of_nonneg_left h (pow_nonneg hs.le q)
    _ = B * (s ^ q * s⁻¹ ^ q) := by ring
    _ = B := by rw [h1, mul_one]

/-- From a scale-weighted bound to an unscaled bound. -/
theorem le_mul_inv_pow_of_scaled_le {s t B : ℝ} (hs : 0 < s) {q : ℕ} (h : s ^ q * t ≤ B) :
    t ≤ B * s⁻¹ ^ q := by
  have h1 : s⁻¹ ^ q * s ^ q = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hs.ne', one_pow]
  calc t = s⁻¹ ^ q * s ^ q * t := by rw [h1, one_mul]
    _ = s⁻¹ ^ q * (s ^ q * t) := mul_assoc _ _ _
    _ ≤ s⁻¹ ^ q * B := mul_le_mul_of_nonneg_left h (pow_nonneg (inv_nonneg.2 hs.le) q)
    _ = B * s⁻¹ ^ q := mul_comm _ _

/-- Lowering the weight by one power of the scale. -/
theorem scaled_succ_le {s t B : ℝ} (hs : 0 < s) {e i : ℕ} (h : s ^ (i + 1) * t ≤ B * s⁻¹ ^ e) :
    s ^ i * t ≤ B * s⁻¹ ^ (e + 1) := by
  have h1 : s⁻¹ * s = 1 := inv_mul_cancel₀ hs.ne'
  calc s ^ i * t = s⁻¹ * s * (s ^ i * t) := by rw [h1, one_mul]
    _ = s⁻¹ * (s ^ (i + 1) * t) := by rw [pow_succ]; ring
    _ ≤ s⁻¹ * (B * s⁻¹ ^ e) := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hs.le)
    _ = B * s⁻¹ ^ (e + 1) := by rw [pow_succ]; ring

/-- A sum of `n + 1 ≤ K + 1` terms, each at most `B`. -/
theorem sum_range_le_of_le {f : ℕ → ℝ} {B : ℝ} {n K : ℕ} (hn : n ≤ K) (hB : 0 ≤ B)
    (h : ∀ q, q ≤ n → f q ≤ B) : ∑ q ∈ Finset.range (n + 1), f q ≤ ((K : ℝ) + 1) * B := by
  have h1 : (n : ℝ) + 1 ≤ K + 1 := by exact_mod_cast Nat.succ_le_succ hn
  calc ∑ q ∈ Finset.range (n + 1), f q
      ≤ ∑ _q ∈ Finset.range (n + 1), B :=
        Finset.sum_le_sum fun q hq => h q (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))
    _ = ((n : ℝ) + 1) * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    _ ≤ ((K : ℝ) + 1) * B := mul_le_mul_of_nonneg_right h1 hB

/-- The slow scale cancels against the chart scale: `Rχ^i ρ^{-i} λ^i = 1` for `λ = ρ / Rχ`. -/
theorem scale_cancel {ρ Rχ lam : ℝ} (hρ : 0 < ρ) (hR : 0 < Rχ) (hlam : lam = ρ / Rχ) (A : ℝ)
    (e i : ℕ) : Rχ ^ i * (ρ⁻¹ ^ i * (A * lam ^ (e + i))) = A * lam ^ e := by
  have h1 : Rχ * ρ⁻¹ * lam = 1 := by
    rw [hlam, div_eq_mul_inv, mul_assoc, ← mul_assoc ρ⁻¹ ρ Rχ⁻¹, inv_mul_cancel₀ hρ.ne', one_mul,
      mul_inv_cancel₀ hR.ne']
  calc Rχ ^ i * (ρ⁻¹ ^ i * (A * lam ^ (e + i)))
      = A * lam ^ e * (Rχ * ρ⁻¹ * lam) ^ i := by
        rw [pow_add, mul_pow, mul_pow]
        ring
    _ = A * lam ^ e := by rw [h1, one_pow, mul_one]

/-- The powers of the scales in one term of the kernel, in additive form. -/
theorem kernel_scale_identity (ρ Rχ : ℝ) (d' a b : ℕ) :
    ρ ^ (d' + a) * (Rχ⁻¹ ^ a * (ρ / Rχ) ^ b) = ρ ^ (d' + a + b) * Rχ⁻¹ ^ (a + b) := by
  rw [div_eq_mul_inv, mul_pow, pow_add ρ (d' + a) b, pow_add Rχ⁻¹ a b]
  ring

/-- The bound for the order-`d` term of the kernel, `d' ≤ d ≤ n ≤ M`, with `λ = ρ / Rχ`. -/
theorem orderTerm_bound_le {ρ Rχ lam A Cp : ℝ} (hρ : 0 < ρ) (hR : 0 < Rχ) (hlam : lam = ρ / Rχ)
    (hA : 0 ≤ A) (hCp : 0 ≤ Cp) {M Kt d' d n : ℕ} (hd' : 2 ≤ d') (hd : d' ≤ d) (hn : d ≤ n)
    (hM : n ≤ M) :
    ρ ^ d * (2 ^ (d - 1) * (2 ^ Kt * ((Kt : ℝ) + 1) * (Cp * Rχ⁻¹ ^ (d - 1 - (d' - 1))) *
        (A * lam ^ (n - d)))) ≤
      2 ^ M * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp) * A * (ρ ^ n * Rχ⁻¹ ^ (n - d')) := by
  obtain ⟨a, rfl⟩ : ∃ a, d = d' + a := ⟨d - d', by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = d' + a + b := ⟨n - (d' + a), by omega⟩
  have e1 : d' + a - 1 - (d' - 1) = a := by omega
  have e2 : d' + a + b - (d' + a) = b := by omega
  have e3 : d' + a + b - d' = a + b := by omega
  have h2 : (2 : ℝ) ^ (d' + a - 1) ≤ 2 ^ M := pow_le_pow_right₀ one_le_two (by omega)
  have hid := kernel_scale_identity ρ Rχ d' a b
  have hnn : 0 ≤ 2 ^ Kt * ((Kt : ℝ) + 1) * Cp * A * (ρ ^ (d' + a + b) * Rχ⁻¹ ^ (a + b)) := by
    positivity
  rw [e1, e2, e3, hlam]
  calc ρ ^ (d' + a) * (2 ^ (d' + a - 1) * (2 ^ Kt * ((Kt : ℝ) + 1) * (Cp * Rχ⁻¹ ^ a) *
        (A * (ρ / Rχ) ^ b)))
      = 2 ^ (d' + a - 1) * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp * A *
          (ρ ^ (d' + a) * (Rχ⁻¹ ^ a * (ρ / Rχ) ^ b))) := by ring
    _ = 2 ^ (d' + a - 1) * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp * A *
          (ρ ^ (d' + a + b) * Rχ⁻¹ ^ (a + b))) := by rw [hid]
    _ ≤ 2 ^ M * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp * A * (ρ ^ (d' + a + b) * Rχ⁻¹ ^ (a + b))) :=
        mul_le_mul_of_nonneg_right h2 hnn
    _ = 2 ^ M * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp) * A * (ρ ^ (d' + a + b) * Rχ⁻¹ ^ (a + b)) := by
        ring

/-- The number of derivative words of length `q`, as a real number. -/
theorem card_word_cast (q : ℕ) :
    ((Finset.univ : Finset (DerivativeWord2 q)).card : ℝ) = 2 ^ q := by
  exact_mod_cast ChartTransport.card_derivativeWord2 q

/-! ### Scale-weighted calculus at a point -/

theorem natCast_le_withTop {i K : ℕ} (h : i ≤ K) :
    ((i : ℕ∞) : WithTop ℕ∞) ≤ ((K : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast h

theorem contDiff_natCast_of_top {f : Vec 2 → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    ContDiff ℝ (n : ℕ∞) f := by
  have htop : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  exact hf.of_le htop

/-- The jets of the zero function vanish. -/
theorem norm_iteratedFDeriv_eq_zero_of_eq_zero {f : Vec 2 → F} (h0 : f = 0) (i : ℕ)
    (y : Vec 2) : ‖iteratedFDeriv ℝ i f y‖ = 0 := by
  have h : iteratedFDeriv ℝ i f y = 0 := by
    rw [h0]
    exact congrFun iteratedFDeriv_zero y
  rw [h, norm_zero]

theorem abs_ite_one_zero_le_one (p : Prop) [Decidable p] :
    |(if p then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

/-- Scale-weighted jets of a constant of size at most one. -/
theorem scaled_const_le {c : ℝ} (hc : |c| ≤ 1) (s : ℝ) (i : ℕ) (y : Vec 2) :
    s ^ i * ‖iteratedFDeriv ℝ i (fun _ : Vec 2 => c) y‖ ≤ 1 := by
  by_cases hi : i = 0
  · subst hi
    rw [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact hc
  · have h : iteratedFDeriv ℝ i (fun _ : Vec 2 => c) y = 0 :=
      congrFun (iteratedFDeriv_const_of_ne hi c) y
    rw [h, norm_zero, mul_zero]
    exact zero_le_one

/-- Scale-weighted Leibniz bound for all orders up to `K`. -/
theorem scaled_smul_le {M : Vec 2 → ℝ} {H : Vec 2 → F} {K : ℕ} (hM : ContDiff ℝ (K : ℕ∞) M)
    (hH : ContDiff ℝ (K : ℕ∞) H) {s A B : ℝ} (hs : 0 < s) (x : Vec 2)
    (hA : ∀ i, i ≤ K → s ^ i * ‖iteratedFDeriv ℝ i M x‖ ≤ A)
    (hB : ∀ i, i ≤ K → s ^ i * ‖iteratedFDeriv ℝ i H x‖ ≤ B) :
    ∀ i, i ≤ K → s ^ i * ‖iteratedFDeriv ℝ i (fun y => M y • H y) x‖ ≤
      2 ^ K * ((K : ℝ) + 1) * A * B := by
  intro i hi
  have hi' := natCast_le_withTop hi
  have hA0 : 0 ≤ A :=
    (mul_nonneg (pow_nonneg hs.le 0) (norm_nonneg _)).trans (hA 0 (Nat.zero_le _))
  have hB0 : 0 ≤ B :=
    (mul_nonneg (pow_nonneg hs.le 0) (norm_nonneg _)).trans (hB 0 (Nat.zero_le _))
  have h := ChartTransport.smul_bound (n := i) (hM.of_le hi') (hH.of_le hi') hs x
    (fun q hq => hA q (hq.trans hi))
  have hsum : ∑ q ∈ Finset.range (i + 1), s ^ q * ‖iteratedFDeriv ℝ q H x‖ ≤
      ((K : ℝ) + 1) * B := sum_range_le_of_le hi hB0 fun q hq => hB q (hq.trans hi)
  have h2 : (2 : ℝ) ^ i ≤ 2 ^ K := pow_le_pow_right₀ one_le_two hi
  have h2A : (2 : ℝ) ^ i * A ≤ 2 ^ K * A := mul_le_mul_of_nonneg_right h2 hA0
  have hS0 : 0 ≤ ∑ q ∈ Finset.range (i + 1), s ^ q * ‖iteratedFDeriv ℝ q H x‖ :=
    Finset.sum_nonneg fun q _ => mul_nonneg (pow_nonneg hs.le q) (norm_nonneg _)
  have hKA0 : 0 ≤ (2 : ℝ) ^ K * A := mul_nonneg (pow_nonneg zero_le_two K) hA0
  calc s ^ i * ‖iteratedFDeriv ℝ i (fun y => M y • H y) x‖
      ≤ 2 ^ i * A * ∑ q ∈ Finset.range (i + 1), s ^ q * ‖iteratedFDeriv ℝ q H x‖ := h
    _ ≤ 2 ^ K * A * (((K : ℝ) + 1) * B) := mul_le_mul h2A hsum hS0 hKA0
    _ = 2 ^ K * ((K : ℝ) + 1) * A * B := by ring

/-- The scalar case of `scaled_smul_le`, written with a product. -/
theorem scaled_mul_le {M H : Vec 2 → ℝ} {K : ℕ} (hM : ContDiff ℝ (K : ℕ∞) M)
    (hH : ContDiff ℝ (K : ℕ∞) H) {s A B : ℝ} (hs : 0 < s) (x : Vec 2)
    (hA : ∀ i, i ≤ K → s ^ i * ‖iteratedFDeriv ℝ i M x‖ ≤ A)
    (hB : ∀ i, i ≤ K → s ^ i * ‖iteratedFDeriv ℝ i H x‖ ≤ B) :
    ∀ i, i ≤ K → s ^ i * ‖iteratedFDeriv ℝ i (fun y => M y * H y) x‖ ≤
      2 ^ K * ((K : ℝ) + 1) * A * B := by
  intro i hi
  exact scaled_smul_le hM hH hs x hA hB i hi

/-- Scale-weighted Faà di Bruno bound at the chart scale for all orders up to `K`. -/
theorem scaled_comp_le {g : Vec 2 → F} {Ψ : Vec 2 → Vec 2} {K : ℕ} (hg : ContDiff ℝ (K : ℕ∞) g)
    (hΨ : ContDiff ℝ (K : ℕ∞) Ψ) {D Rχ B : ℝ} (hD : 1 ≤ D) (hR : 0 < Rχ)
    (hJ : ChartTransport.JetBound Ψ K D Rχ) (x : Vec 2)
    (hB : ∀ i, i ≤ K → Rχ ^ i * ‖iteratedFDeriv ℝ i g (Ψ x)‖ ≤ B) :
    ∀ j, j ≤ K → Rχ ^ j * ‖iteratedFDeriv ℝ j (g ∘ Ψ) x‖ ≤
      (K.factorial : ℝ) * D ^ K * ((K : ℝ) + 1) * B := by
  intro j hj
  have hj' := natCast_le_withTop hj
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hB0 : 0 ≤ B :=
    (mul_nonneg (pow_nonneg hR.le 0) (norm_nonneg _)).trans (hB 0 (Nat.zero_le _))
  have h := ChartTransport.scaled_comp_bound (n := j) (hg.of_le hj') (hΨ.of_le hj') hD hR le_rfl x
    (fun p hp1 hpj => hJ p hp1 (hpj.trans hj) x)
  have hsum : ∑ i ∈ Finset.range (j + 1), Rχ ^ i * ‖iteratedFDeriv ℝ i g (Ψ x)‖ ≤
      ((K : ℝ) + 1) * B := sum_range_le_of_le hj hB0 fun q hq => hB q (hq.trans hj)
  have h1 : (j.factorial : ℝ) ≤ K.factorial := by exact_mod_cast Nat.factorial_le hj
  have h2 : D ^ j ≤ D ^ K := pow_le_pow_right₀ hD hj
  have hfq : (j.factorial : ℝ) * D ^ j ≤ K.factorial * D ^ K :=
    mul_le_mul h1 h2 (pow_nonneg hD0 j) (Nat.cast_nonneg _)
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (j + 1), Rχ ^ i * ‖iteratedFDeriv ℝ i g (Ψ x)‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg hR.le i) (norm_nonneg _)
  have hK0 : 0 ≤ (K.factorial : ℝ) * D ^ K := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD0 K)
  calc Rχ ^ j * ‖iteratedFDeriv ℝ j (g ∘ Ψ) x‖
      ≤ j.factorial * D ^ j *
          ∑ i ∈ Finset.range (j + 1), Rχ ^ i * ‖iteratedFDeriv ℝ i g (Ψ x)‖ := h
    _ ≤ K.factorial * D ^ K * (((K : ℝ) + 1) * B) := mul_le_mul hfq hsum hS0 hK0
    _ = (K.factorial : ℝ) * D ^ K * ((K : ℝ) + 1) * B := by ring

/-- Scale-weighted bound for a finite sum. -/
theorem scaled_sum_le {ι : Type*} (S : Finset ι) {f : ι → Vec 2 → F} {K : ℕ}
    (hf : ∀ a ∈ S, ContDiff ℝ (K : ℕ∞) (f a)) {s : ℝ} (hs : 0 ≤ s) (x : Vec 2) (b : ι → ℝ)
    (hb : ∀ a ∈ S, ∀ i, i ≤ K → s ^ i * ‖iteratedFDeriv ℝ i (f a) x‖ ≤ b a) :
    ∀ i, i ≤ K → s ^ i * ‖iteratedFDeriv ℝ i (fun y => ∑ a ∈ S, f a y) x‖ ≤ ∑ a ∈ S, b a := by
  intro i hi
  have hi' := natCast_le_withTop hi
  have hder : iteratedFDeriv ℝ i (fun y => ∑ a ∈ S, f a y) x =
      ∑ a ∈ S, iteratedFDeriv ℝ i (f a) x :=
    iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := i) (x := x) (u := S) (f := f)
      (fun a ha => ((hf a ha).of_le hi').contDiffAt)
  rw [hder]
  calc s ^ i * ‖∑ a ∈ S, iteratedFDeriv ℝ i (f a) x‖
      ≤ s ^ i * ∑ a ∈ S, ‖iteratedFDeriv ℝ i (f a) x‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hs i)
    _ = ∑ a ∈ S, s ^ i * ‖iteratedFDeriv ℝ i (f a) x‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ a ∈ S, b a := Finset.sum_le_sum fun a ha => hb a ha i hi

/-- Scale-weighted bound for a constant multiple. -/
theorem scaled_const_smul_le {f : Vec 2 → F} {K : ℕ} (hf : ContDiff ℝ (K : ℕ∞) f) (r : ℝ)
    {s B : ℝ} (x : Vec 2) (hB : ∀ i, i ≤ K → s ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ B) :
    ∀ i, i ≤ K → s ^ i * ‖iteratedFDeriv ℝ i (fun y => r • f y) x‖ ≤ |r| * B := by
  intro i hi
  have hi' := natCast_le_withTop hi
  have hder : iteratedFDeriv ℝ i (fun y => r • f y) x = r • iteratedFDeriv ℝ i f x :=
    iteratedFDeriv_const_smul_apply' (a := r) (f := f) (x := x) (i := i)
      ((hf.of_le hi').contDiffAt)
  rw [hder, norm_smul, Real.norm_eq_abs]
  calc s ^ i * (|r| * ‖iteratedFDeriv ℝ i f x‖)
      = |r| * (s ^ i * ‖iteratedFDeriv ℝ i f x‖) := by ring
    _ ≤ |r| * B := mul_le_mul_of_nonneg_left (hB i hi) (abs_nonneg r)

/-- Scale-weighted jets of the Jacobian entries of a chart with normalized jets. -/
theorem jacMatrix_scaled_bound {Φ : Vec 2 → Vec 2} {N : ℕ} {D Rχ : ℝ} (hR : 0 < Rχ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hJ : ChartTransport.JetBound Φ N D Rχ) (k l : Fin 2)
    (y : Vec 2) (q : ℕ) (hq : q + 1 ≤ N) :
    Rχ ^ q * ‖iteratedFDeriv ℝ q (fun z => jacMatrix Φ z k l) y‖ ≤ D := by
  have h1 := ChartTransport.norm_iteratedFDeriv_jac_entry (n := q) (i := q)
    (contDiff_natCast_of_top hΦ (q + 1)) le_rfl k l (c := 1) (by simp) y
  have h2 := hJ (q + 1) (by omega) hq y
  simp only [Nat.add_sub_cancel] at h2
  have e : (fun z => jacMatrix Φ z k l) = fun z => 1 * jacMatrix Φ z k l :=
    funext fun z => (one_mul _).symm
  rw [e]
  exact scaled_le_of_le_inv_pow hR q (h1.trans h2)

/-- A directional derivative costs one order. -/
theorem norm_iteratedFDeriv_fderiv_apply_le {P : Vec 2 → ℝ} {K : ℕ}
    (hP : ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) P) (a : Fin 2) {i : ℕ} (hi : i ≤ K) (y : Vec 2) :
    ‖iteratedFDeriv ℝ i (fun z => fderiv ℝ P z (basisVec a)) y‖ ≤
      ‖iteratedFDeriv ℝ (i + 1) P y‖ := by
  have hfd : ContDiff ℝ (K : ℕ∞) (fderiv ℝ P) := hP.fderiv_right (by simp)
  have hi' := natCast_le_withTop hi
  have h := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ P)
    (c := (basisVec a : Vec 2)) (x := y) (N := (i : ℕ∞)) (n := i)
    (hfd.of_le hi').contDiffAt le_rfl
  calc ‖iteratedFDeriv ℝ i (fun z => fderiv ℝ P z (basisVec a)) y‖
      ≤ ‖(basisVec a : Vec 2)‖ * ‖iteratedFDeriv ℝ i (fderiv ℝ P) y‖ := h
    _ = ‖iteratedFDeriv ℝ (i + 1) P y‖ := by
        rw [ChartTransport.norm_basisVec, one_mul, norm_iteratedFDeriv_fderiv]

/-! ### Jets of the chain-rule coefficients -/

/-- One step of the recursion for the chain-rule coefficients, in scale-weighted form. -/
theorem chainStep_scaled_le {P₁ P₂ J : Vec 2 → ℝ} {I : ℕ}
    (hP₁ : ContDiff ℝ ((I + 1 : ℕ) : ℕ∞) P₁) (hP₂ : ContDiff ℝ (I : ℕ∞) P₂)
    (hJc : ContDiff ℝ (I : ℕ∞) J) (a : Fin 2) {s B₁ B₂ D : ℝ} (hs : 0 < s) (y : Vec 2)
    (h₁ : ∀ i, i ≤ I → s ^ i * ‖iteratedFDeriv ℝ (i + 1) P₁ y‖ ≤ B₁)
    (h₂ : ∀ i, i ≤ I → s ^ i * ‖iteratedFDeriv ℝ i P₂ y‖ ≤ B₂)
    (hJ : ∀ i, i ≤ I → s ^ i * ‖iteratedFDeriv ℝ i J y‖ ≤ D) :
    ∀ i, i ≤ I → s ^ i * ‖iteratedFDeriv ℝ i
        (fun z => fderiv ℝ P₁ z (basisVec a) + P₂ z * J z) y‖ ≤
      B₁ + 2 ^ I * ((I : ℝ) + 1) * B₂ * D := by
  intro i hi
  have hi' := natCast_le_withTop hi
  have hfd0 : ContDiff ℝ (I : ℕ∞) (fderiv ℝ P₁) := hP₁.fderiv_right (by simp)
  have hfd : ContDiff ℝ (I : ℕ∞) (fun z => fderiv ℝ P₁ z (basisVec a)) :=
    hfd0.clm_apply contDiff_const
  have hmul : ContDiff ℝ (I : ℕ∞) (fun z => P₂ z * J z) := hP₂.mul hJc
  have hadd := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := i)
    (f := fun z => fderiv ℝ P₁ z (basisVec a)) (g := fun z => P₂ z * J z) (x := y)
    (hfd.of_le hi').contDiffAt (hmul.of_le hi').contDiffAt
  have e : (fun z => fderiv ℝ P₁ z (basisVec a) + P₂ z * J z) =
      (fun z => fderiv ℝ P₁ z (basisVec a)) + fun z => P₂ z * J z := rfl
  have ha := norm_iteratedFDeriv_fderiv_apply_le hP₁ a hi y
  have hb := scaled_mul_le hP₂ hJc hs y h₂ hJ i hi
  rw [e, hadd]
  calc s ^ i * ‖iteratedFDeriv ℝ i (fun z => fderiv ℝ P₁ z (basisVec a)) y +
        iteratedFDeriv ℝ i (fun z => P₂ z * J z) y‖
      ≤ s ^ i * (‖iteratedFDeriv ℝ i (fun z => fderiv ℝ P₁ z (basisVec a)) y‖ +
        ‖iteratedFDeriv ℝ i (fun z => P₂ z * J z) y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hs.le i)
    _ = s ^ i * ‖iteratedFDeriv ℝ i (fun z => fderiv ℝ P₁ z (basisVec a)) y‖ +
        s ^ i * ‖iteratedFDeriv ℝ i (fun z => P₂ z * J z) y‖ := mul_add _ _ _
    _ ≤ B₁ + 2 ^ I * ((I : ℝ) + 1) * B₂ * D :=
        add_le_add ((mul_le_mul_of_nonneg_left ha (pow_nonneg hs.le i)).trans (h₁ i hi)) hb

/-- Jets of the chain-rule coefficients, in scale-weighted form. -/
theorem chainCoeff_scaled_bound (D : ℝ) (hD : 1 ≤ D) (m : ℕ) : ∀ I : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : Vec 2 → Vec 2) (Rχ : ℝ), 0 < Rχ → ContDiff ℝ (⊤ : ℕ∞) Φ →
      ChartTransport.JetBound Φ (I + m) D Rχ →
      ∀ i, i ≤ I → ∀ (α : DerivativeWord2 m) (m' : ℕ) (β : DerivativeWord2 m') (y : Vec 2),
        Rχ ^ i * ‖iteratedFDeriv ℝ i (chainCoeff Φ m α m' β) y‖ ≤ C * Rχ⁻¹ ^ (m - m') := by
  induction m with
  | zero =>
    intro _
    refine ⟨1, zero_le_one, ?_⟩
    intro _ Rχ _ _ _ i _ _ m' _ y
    have e0 : 0 - m' = 0 := by omega
    rw [chainCoeff_zero, e0, pow_zero, mul_one]
    exact scaled_const_le (abs_ite_one_zero_le_one (m' = 0)) Rχ i y
  | succ m ih =>
    intro I
    obtain ⟨C₁, hC₁0, hC₁⟩ := ih (I + 1)
    have hD0 : 0 ≤ D := zero_le_one.trans hD
    have hC0 : 0 ≤ C₁ + 2 ^ I * ((I : ℝ) + 1) * C₁ * D := by positivity
    refine ⟨C₁ + 2 ^ I * ((I : ℝ) + 1) * C₁ * D, hC0, ?_⟩
    intro Φ Rχ hR hΦ hJ i hi α m' β y
    have hinv : 0 ≤ Rχ⁻¹ := inv_nonneg.2 hR.le
    have hJ' : ChartTransport.JetBound Φ (I + 1 + m) D Rχ := by
      intro p hp1 hp z
      exact hJ p hp1 (by omega) z
    cases m' with
    | zero =>
      rw [norm_iteratedFDeriv_eq_zero_of_eq_zero (chainCoeff_succ_zero_eq_zero Φ m α β) i y,
        mul_zero]
      exact mul_nonneg hC0 (pow_nonneg hinv _)
    | succ m' =>
      have e : m + 1 - (m' + 1) = m - m' := by omega
      rw [chainCoeff_succ_succ, e]
      have h₂ : ∀ q, q ≤ I → Rχ ^ q * ‖iteratedFDeriv ℝ q
          (chainCoeff Φ m (fun i => α i.castSucc) m' (fun i => β i.castSucc)) y‖ ≤
            C₁ * Rχ⁻¹ ^ (m - m') :=
        fun q hq => hC₁ Φ Rχ hR hΦ hJ' q (by omega) (fun i => α i.castSucc) m'
          (fun i => β i.castSucc) y
      have h₁ : ∀ q, q ≤ I → Rχ ^ q * ‖iteratedFDeriv ℝ (q + 1)
          (chainCoeff Φ m (fun i => α i.castSucc) (m' + 1) β) y‖ ≤ C₁ * Rχ⁻¹ ^ (m - m') := by
        intro q hq
        by_cases hlt : m' < m
        · have h := scaled_succ_le hR (hC₁ Φ Rχ hR hΦ hJ' (q + 1) (by omega)
            (fun i => α i.castSucc) (m' + 1) β y)
          have e' : m - (m' + 1) + 1 = m - m' := by omega
          rw [e'] at h
          exact h
        · rw [norm_iteratedFDeriv_eq_zero_of_eq_zero
            (chainCoeff_eq_zero_of_lt Φ m (fun i => α i.castSucc) (m' + 1) β (by omega))
            (q + 1) y, mul_zero]
          exact mul_nonneg hC₁0 (pow_nonneg hinv _)
      have hJs : ∀ q, q ≤ I → Rχ ^ q * ‖iteratedFDeriv ℝ q
          (fun z => jacMatrix Φ z (β (Fin.last m')) (α (Fin.last m))) y‖ ≤ D :=
        fun q hq => jacMatrix_scaled_bound hR hΦ hJ (β (Fin.last m')) (α (Fin.last m)) y q
          (by omega)
      have h := chainStep_scaled_le
        (contDiff_natCast_of_top
          (contDiff_chainCoeff hΦ m (fun i => α i.castSucc) (m' + 1) β) (I + 1))
        (contDiff_natCast_of_top
          (contDiff_chainCoeff hΦ m (fun i => α i.castSucc) m' (fun i => β i.castSucc)) I)
        (contDiff_natCast_of_top
          (contDiff_jacMatrix hΦ (β (Fin.last m')) (α (Fin.last m))) I)
        (α (Fin.last m)) hR y h₁ h₂ hJs i hi
      exact h.trans (le_of_eq (by ring))

/-! ### Scale-weighted jets, uniformly in the point -/

/-- `f` is `C^K` and its jets through order `K`, weighted by the powers of the scale `s`, are
bounded by `B` at every point. -/
structure ScaledJet (K : ℕ) (s : ℝ) (f : Vec 2 → F) (B : ℝ) : Prop where
  contDiff : ContDiff ℝ (K : ℕ∞) f
  bound : ∀ (x : Vec 2) (i : ℕ), i ≤ K → s ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ B

theorem scaledJet_mono {K : ℕ} {s B B' : ℝ} {f : Vec 2 → F} (h : ScaledJet K s f B)
    (hB : B ≤ B') : ScaledJet K s f B' :=
  ⟨h.contDiff, fun x i hi => (h.bound x i hi).trans hB⟩

theorem scaledJet_of_eq_zero {K : ℕ} {f : Vec 2 → F} (hf : ContDiff ℝ (K : ℕ∞) f)
    (h0 : f = 0) (s : ℝ) : ScaledJet K s f 0 := by
  refine ⟨hf, fun x i _ => le_of_eq ?_⟩
  rw [norm_iteratedFDeriv_eq_zero_of_eq_zero h0 i x, mul_zero]

theorem scaledJet_smul {K : ℕ} {s A B : ℝ} {M : Vec 2 → ℝ} {H : Vec 2 → F} (hs : 0 < s)
    (hM : ScaledJet K s M A) (hH : ScaledJet K s H B) :
    ScaledJet K s (fun y => M y • H y) (2 ^ K * ((K : ℝ) + 1) * A * B) :=
  ⟨hM.contDiff.smul hH.contDiff, fun x i hi =>
    scaled_smul_le hM.contDiff hH.contDiff hs x (hM.bound x) (hH.bound x) i hi⟩

theorem scaledJet_sum {ι : Type*} (S : Finset ι) {K : ℕ} {s : ℝ} (hs : 0 ≤ s)
    {f : ι → Vec 2 → F} {b : ι → ℝ} (hf : ∀ a ∈ S, ScaledJet K s (f a) (b a)) :
    ScaledJet K s (fun y => ∑ a ∈ S, f a y) (∑ a ∈ S, b a) :=
  ⟨ContDiff.sum fun a ha => (hf a ha).contDiff, fun x i hi =>
    scaled_sum_le S (fun a ha => (hf a ha).contDiff) hs x b
      (fun a ha q hq => (hf a ha).bound x q hq) i hi⟩

theorem scaledJet_sum_card {ι : Type*} (S : Finset ι) {K : ℕ} {s b : ℝ} (hs : 0 ≤ s)
    {f : ι → Vec 2 → F} (hf : ∀ a ∈ S, ScaledJet K s (f a) b) :
    ScaledJet K s (fun y => ∑ a ∈ S, f a y) (S.card * b) := by
  have h := scaledJet_sum S hs (b := fun _ => b) hf
  have e : (∑ _a ∈ S, b) = S.card * b := by rw [Finset.sum_const, nsmul_eq_mul]
  exact scaledJet_mono h (le_of_eq e)

theorem scaledJet_add {K : ℕ} {s A B : ℝ} {f g : Vec 2 → F} (hs : 0 ≤ s)
    (hf : ScaledJet K s f A) (hg : ScaledJet K s g B) :
    ScaledJet K s (fun y => f y + g y) (A + B) := by
  have h := scaledJet_sum (Finset.univ : Finset (Fin 2)) hs
    (f := (![f, g] : Fin 2 → Vec 2 → F)) (b := (![A, B] : Fin 2 → ℝ))
    (fun a _ => by
      fin_cases a
      · exact hf
      · exact hg)
  have e1 : (fun y => ∑ a : Fin 2, (![f, g] : Fin 2 → Vec 2 → F) a y) = fun y => f y + g y := by
    funext y
    rw [Fin.sum_univ_two]
    rfl
  have e2 : (∑ a : Fin 2, (![A, B] : Fin 2 → ℝ) a) = A + B := by
    rw [Fin.sum_univ_two]
    rfl
  rw [← e1, ← e2]
  exact h

theorem scaledJet_const_smul {K : ℕ} {s B : ℝ} {f : Vec 2 → F} (r : ℝ) (h : ScaledJet K s f B) :
    ScaledJet K s (fun y => r • f y) (|r| * B) :=
  ⟨h.contDiff.const_smul r, fun x i hi =>
    scaled_const_smul_le h.contDiff r x (h.bound x) i hi⟩

theorem scaledJet_comp {K : ℕ} {D Rχ B : ℝ} {g : Vec 2 → F} {Ψ : Vec 2 → Vec 2} (hD : 1 ≤ D)
    (hR : 0 < Rχ) (hg : ScaledJet K Rχ g B) (hΨ : ContDiff ℝ (K : ℕ∞) Ψ)
    (hJ : ChartTransport.JetBound Ψ K D Rχ) :
    ScaledJet K Rχ (fun x => g (Ψ x)) ((K.factorial : ℝ) * D ^ K * ((K : ℝ) + 1) * B) :=
  ⟨hg.contDiff.comp hΨ, fun x j hj =>
    scaled_comp_le hg.contDiff hΨ hD hR hJ x (fun i hi => hg.bound (Ψ x) i hi) j hj⟩

/-- A letter in the slow variable `ρ⁻¹ y`, with slow jets of size `A λ^{e + i}`, `λ = ρ / Rχ`. -/
theorem scaledJet_letter {K : ℕ} {W : Vec 2 → F} (hW : ContDiff ℝ (K : ℕ∞) W)
    {ρ Rχ lam A : ℝ} (hρ : 0 < ρ) (hR : 0 < Rχ) (hlam : lam = ρ / Rχ) (e : ℕ)
    (hb : ∀ i, i ≤ K → ∀ X, ‖iteratedFDeriv ℝ i W X‖ ≤ A * lam ^ (e + i)) :
    ScaledJet K Rχ (fun y => W (ρ⁻¹ • y)) (A * lam ^ e) := by
  refine ⟨hW.comp (contDiff_const_smul ρ⁻¹), fun x i hi => ?_⟩
  have hi' := natCast_le_withTop hi
  have hder : iteratedFDeriv ℝ i (fun y => W (ρ⁻¹ • y)) x =
      ρ⁻¹ ^ i • iteratedFDeriv ℝ i W (ρ⁻¹ • x) :=
    congrFun (iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := i) ρ⁻¹ (hW.of_le hi')) x
  rw [hder, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (inv_pos.2 hρ) i)]
  calc Rχ ^ i * (ρ⁻¹ ^ i * ‖iteratedFDeriv ℝ i W (ρ⁻¹ • x)‖)
      ≤ Rχ ^ i * (ρ⁻¹ ^ i * (A * lam ^ (e + i))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb i hi _)
          (pow_nonneg (inv_nonneg.2 hρ.le) i)) (pow_nonneg hR.le i)
    _ = A * lam ^ e := scale_cancel hρ hR hlam A e i

/-- The chain-rule coefficients of all orders `m ≤ M`, with one constant. -/
theorem chainCoeff_scaledJet_uniform (D : ℝ) (hD : 1 ≤ D) (M I : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : Vec 2 → Vec 2) (Rχ : ℝ), 0 < Rχ → ContDiff ℝ (⊤ : ℕ∞) Φ →
      ChartTransport.JetBound Φ (I + M) D Rχ →
      ∀ m, m ≤ M → ∀ (α : DerivativeWord2 m) (m' : ℕ) (β : DerivativeWord2 m'),
        ScaledJet I Rχ (chainCoeff Φ m α m' β) (C * Rχ⁻¹ ^ (m - m')) := by
  choose Cf hCf0 hCf using fun m => chainCoeff_scaled_bound D hD m I
  refine ⟨∑ m ∈ Finset.range (M + 1), Cf m, Finset.sum_nonneg fun m _ => hCf0 m, ?_⟩
  intro Φ Rχ hR hΦ hJ m hm α m' β
  have hJm : ChartTransport.JetBound Φ (I + m) D Rχ := by
    intro p hp1 hp y
    exact hJ p hp1 (by omega) y
  have hle : Cf m ≤ ∑ m ∈ Finset.range (M + 1), Cf m :=
    Finset.single_le_sum (f := Cf) (fun m _ => hCf0 m)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hm))
  refine ⟨contDiff_natCast_of_top (contDiff_chainCoeff hΦ m α m' β) I, fun y i hi => ?_⟩
  exact (hCf m Φ Rχ hR hΦ hJm i hi α m' β y).trans
    (mul_le_mul_of_nonneg_right hle (pow_nonneg (inv_nonneg.2 hR.le) _))

/-! ### The kernel of one pulse in the label variable -/

/-- The order-`n`, row-`l` factor of the kernel of one pulse, as a function of the label `y`. -/
def kernelTerm (ρ : ℝ) (chart : Vec 2 → Vec 2)
    (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → F) (m' : ℕ)
    (β : DerivativeWord2 m') (n : ℕ) (l : Fin 2) (y : Vec 2) : F :=
  ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
    chainCoeff chart (d - 1) α m' β y • W n d α l (ρ⁻¹ • y)

/-- The kernel of one pulse in the label variable, without the orders `n < d'`, which vanish. -/
def labelKernel (c ρ εc : ℝ) (M : ℕ) (chart : Vec 2 → Vec 2)
    (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → F) (d' : ℕ)
    (β : DerivativeWord2 (d' - 1)) (k' : Fin 2) (y : Vec 2) : F :=
  ∑ n ∈ Finset.Icc d' M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart y k' l •
    kernelTerm ρ chart W (d' - 1) β n l y

/-- Lowering the tested order to `d'` kills the orders `n < d'`. -/
theorem kernelTerm_eq_zero (ρ : ℝ) (chart : Vec 2 → Vec 2)
    (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → F) {d' n : ℕ}
    (β : DerivativeWord2 (d' - 1)) (l : Fin 2) (hn : n < d') (y : Vec 2) :
    kernelTerm ρ chart W (d' - 1) β n l y = 0 := by
  have e : kernelTerm ρ chart W (d' - 1) β n l y = ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
      ∑ α : DerivativeWord2 (d - 1),
        chainCoeff chart (d - 1) α (d' - 1) β y • W n d α l (ρ⁻¹ • y) := rfl
  rw [e]
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨hd2, hdn⟩ := Finset.mem_Icc.1 hd
  have hz : (∑ α : DerivativeWord2 (d - 1),
      chainCoeff chart (d - 1) α (d' - 1) β y • W n d α l (ρ⁻¹ • y)) = 0 :=
    Finset.sum_eq_zero fun α _ => by
      have h0 : chainCoeff chart (d - 1) α (d' - 1) β y = 0 :=
        congrFun (chainCoeff_eq_zero_of_lt chart (d - 1) α (d' - 1) β (by omega)) y
      show chainCoeff chart (d - 1) α (d' - 1) β y • W n d α l (ρ⁻¹ • y) = 0
      rw [h0, zero_smul]
  show ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
      chainCoeff chart (d - 1) α (d' - 1) β y • W n d α l (ρ⁻¹ • y) = 0
  rw [hz, smul_zero]

/-- The kernel of one pulse is the label kernel composed with the label map. -/
theorem pulseKernel_eq_labelKernel (c ρ εc : ℝ) (M : ℕ) (chart label : Vec 2 → Vec 2)
    (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → F) {d' : ℕ} (hd' : 2 ≤ d')
    (β : DerivativeWord2 (d' - 1)) (k' : Fin 2) (x : Vec 2) :
    pulseKernel c ρ εc M chart label W (d' - 1) β k' x =
      labelKernel c ρ εc M chart W d' β k' (label x) := by
  have e₁ : pulseKernel c ρ εc M chart label W (d' - 1) β k' x =
      ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart (label x) k' l •
        kernelTerm ρ chart W (d' - 1) β n l (label x) := rfl
  have e₂ : labelKernel c ρ εc M chart W d' β k' (label x) =
      ∑ n ∈ Finset.Icc d' M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart (label x) k' l •
        kernelTerm ρ chart W (d' - 1) β n l (label x) := rfl
  rw [e₁, e₂]
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_left hd') fun n hn hn' => ?_).symm
  have hlt : n < d' := by
    have hnM := (Finset.mem_Icc.1 hn).2
    by_contra hcon
    exact hn' (Finset.mem_Icc.2 ⟨by omega, hnM⟩)
  have hsum : (∑ l : Fin 2, jacMatrix chart (label x) k' l •
      kernelTerm ρ chart W (d' - 1) β n l (label x)) = 0 :=
    Finset.sum_eq_zero fun l _ => by
      show jacMatrix chart (label x) k' l • kernelTerm ρ chart W (d' - 1) β n l (label x) = 0
      rw [kernelTerm_eq_zero ρ chart W (d' := d') (n := n) β l hlt (label x), smul_zero]
  show (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart (label x) k' l •
      kernelTerm ρ chart W (d' - 1) β n l (label x) = 0
  rw [hsum, smul_zero]

/-- The order-`d` term of the kernel: the sum over the words `α` of the chain-rule coefficients
times the letters (the term for fixed `(n, l, d, α)` is `scaledJet_smul` of `scaledJet_letter`). -/
theorem scaledJet_orderTerm {q K : ℕ} {ρ Rχ lam A Bp : ℝ} (hρ : 0 < ρ) (hR : 0 < Rχ)
    (hlam : lam = ρ / Rχ) (d e : ℕ) {P : DerivativeWord2 q → Vec 2 → ℝ}
    {W : DerivativeWord2 q → Vec 2 → F} (hP : ∀ α, ScaledJet K Rχ (P α) Bp)
    (hW : ∀ α, ContDiff ℝ (K : ℕ∞) (W α))
    (hWb : ∀ α, ∀ i, i ≤ K → ∀ X, ‖iteratedFDeriv ℝ i (W α) X‖ ≤ A * lam ^ (e + i)) :
    ScaledJet K Rχ (fun y => ρ ^ d • ∑ α : DerivativeWord2 q, P α y • W α (ρ⁻¹ • y))
      (ρ ^ d * (2 ^ q * (2 ^ K * ((K : ℝ) + 1) * Bp * (A * lam ^ e)))) := by
  have h1 : ∀ α ∈ (Finset.univ : Finset (DerivativeWord2 q)),
      ScaledJet K Rχ (fun y => P α y • W α (ρ⁻¹ • y))
        (2 ^ K * ((K : ℝ) + 1) * Bp * (A * lam ^ e)) :=
    fun α _ => scaledJet_smul hR (hP α) (scaledJet_letter (hW α) hρ hR hlam e (hWb α))
  refine scaledJet_mono (scaledJet_const_smul (ρ ^ d)
    (scaledJet_sum_card (Finset.univ : Finset (DerivativeWord2 q)) hR.le h1)) (le_of_eq ?_)
  rw [abs_of_pos (pow_pos hρ d), card_word_cast q]

/-- The order-`n`, row-`l` factor of the kernel, for `d' ≤ n ≤ M`. -/
theorem scaledJet_kernelTerm {M Kt : ℕ} {ρ Rχ lam A Cp : ℝ} (hρ : 0 < ρ) (hR : 0 < Rχ)
    (hlam : lam = ρ / Rχ) (hA : 0 ≤ A) (hCp : 0 ≤ Cp) {chart : Vec 2 → Vec 2}
    (hchart : ContDiff ℝ (⊤ : ℕ∞) chart)
    {W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → F}
    (hP : ∀ m, m ≤ M → ∀ (α : DerivativeWord2 m) (m' : ℕ) (β : DerivativeWord2 m'),
      ScaledJet Kt Rχ (chainCoeff chart m α m' β) (Cp * Rχ⁻¹ ^ (m - m')))
    {d' : ℕ} (hd' : 2 ≤ d') (β : DerivativeWord2 (d' - 1)) {n : ℕ} (hn : d' ≤ n) (hnM : n ≤ M)
    (hW : ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2),
      ContDiff ℝ (Kt : ℕ∞) (W n d α l))
    (hWb : ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2),
      ∀ i, i ≤ Kt → ∀ X, ‖iteratedFDeriv ℝ i (W n d α l) X‖ ≤ A * lam ^ (n - d + i))
    (l : Fin 2) :
    ScaledJet Kt Rχ (kernelTerm ρ chart W (d' - 1) β n l)
      ((M : ℝ) * (2 ^ M * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp)) * A * (ρ ^ n * Rχ⁻¹ ^ (n - d'))) := by
  have hb0 : 0 ≤ 2 ^ M * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp) * A * (ρ ^ n * Rχ⁻¹ ^ (n - d')) := by
    positivity
  have hterm : ∀ d ∈ Finset.Icc 2 n, ScaledJet Kt Rχ
      (fun y => ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
        chainCoeff chart (d - 1) α (d' - 1) β y • W n d α l (ρ⁻¹ • y))
      (2 ^ M * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp) * A * (ρ ^ n * Rχ⁻¹ ^ (n - d'))) := by
    intro d hd
    obtain ⟨hd2, hdn⟩ := Finset.mem_Icc.1 hd
    by_cases hlt : d < d'
    · have hP0 : ∀ α : DerivativeWord2 (d - 1),
          ScaledJet Kt Rχ (chainCoeff chart (d - 1) α (d' - 1) β) 0 := fun α =>
        scaledJet_of_eq_zero
          (contDiff_natCast_of_top (contDiff_chainCoeff hchart (d - 1) α (d' - 1) β) Kt)
          (chainCoeff_eq_zero_of_lt chart (d - 1) α (d' - 1) β (by omega)) Rχ
      have hz : ρ ^ d * (2 ^ (d - 1) * (2 ^ Kt * ((Kt : ℝ) + 1) * 0 * (A * lam ^ (n - d)))) =
          0 := by ring
      exact scaledJet_mono (scaledJet_orderTerm hρ hR hlam d (n - d) hP0
        (fun α => hW d hd2 hdn α l) (fun α => hWb d hd2 hdn α l))
        (hz.le.trans hb0)
    · have hge : d' ≤ d := by omega
      exact scaledJet_mono (scaledJet_orderTerm hρ hR hlam d (n - d)
        (fun α => hP (d - 1) (by omega) α (d' - 1) β)
        (fun α => hW d hd2 hdn α l) (fun α => hWb d hd2 hdn α l))
        (orderTerm_bound_le hρ hR hlam hA hCp hd' hge hdn hnM)
  have hcard : ((Finset.Icc 2 n).card : ℝ) ≤ M := by
    have h : (Finset.Icc 2 n).card ≤ M := by
      rw [Nat.card_Icc]
      omega
    exact_mod_cast h
  have e : kernelTerm ρ chart W (d' - 1) β n l = fun y => ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
      ∑ α : DerivativeWord2 (d - 1),
        chainCoeff chart (d - 1) α (d' - 1) β y • W n d α l (ρ⁻¹ • y) := rfl
  rw [e]
  refine scaledJet_mono (scaledJet_sum_card (Finset.Icc 2 n) hR.le hterm) ?_
  calc ((Finset.Icc 2 n).card : ℝ) *
        (2 ^ M * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp) * A * (ρ ^ n * Rχ⁻¹ ^ (n - d')))
      ≤ (M : ℝ) * (2 ^ M * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp) * A * (ρ ^ n * Rχ⁻¹ ^ (n - d'))) :=
        mul_le_mul_of_nonneg_right hcard hb0
    _ = (M : ℝ) * (2 ^ M * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp)) * A * (ρ ^ n * Rχ⁻¹ ^ (n - d')) := by
        ring

/-- The order-`n` part of a kernel: Jacobian rows times row factors, summed over the rows. -/
theorem scaledJet_kernelOrder {Kt : ℕ} {c εc Rχ D B : ℝ} (hc : 0 < c) (hε : 0 ≤ εc)
    (hR : 0 < Rχ) (n : ℕ) {J : Fin 2 → Vec 2 → ℝ} {T : Fin 2 → Vec 2 → F}
    (hJ : ∀ l, ScaledJet Kt Rχ (J l) D) (hT : ∀ l, ScaledJet Kt Rχ (T l) B) :
    ScaledJet Kt Rχ (fun y => (c⁻¹ * εc ^ n) • ∑ l : Fin 2, J l y • T l y)
      (c⁻¹ * εc ^ n * (2 * (2 ^ Kt * ((Kt : ℝ) + 1) * D * B))) := by
  have h1 : ∀ l ∈ (Finset.univ : Finset (Fin 2)),
      ScaledJet Kt Rχ (fun y => J l y • T l y) (2 ^ Kt * ((Kt : ℝ) + 1) * D * B) :=
    fun l _ => scaledJet_smul hR (hJ l) (hT l)
  have hcard : ((Finset.univ : Finset (Fin 2)).card : ℝ) = 2 := by simp
  refine scaledJet_mono (scaledJet_const_smul (c⁻¹ * εc ^ n)
    (scaledJet_sum_card (Finset.univ : Finset (Fin 2)) hR.le h1)) (le_of_eq ?_)
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.2 hc.le) (pow_nonneg hε n)), hcard]

/-- Jets of the kernel in the label variable, weighted at the chart scale. -/
theorem scaledJet_labelKernel {Kt : ℕ} {c εc Rχ D : ℝ} (hc : 0 < c) (hε : 0 ≤ εc) (hR : 0 < Rχ)
    (ρ : ℝ) (M : ℕ) {chart : Vec 2 → Vec 2}
    (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → F) {d' : ℕ}
    (β : DerivativeWord2 (d' - 1)) (k' : Fin 2) (A : ℕ → ℝ) (Kc : ℝ)
    (hJ : ∀ l, ScaledJet Kt Rχ (fun y => jacMatrix chart y k' l) D)
    (hT : ∀ n, d' ≤ n → n ≤ M → ∀ l, ScaledJet Kt Rχ (kernelTerm ρ chart W (d' - 1) β n l)
      (Kc * A n * (ρ ^ n * Rχ⁻¹ ^ (n - d')))) :
    ScaledJet Kt Rχ (labelKernel c ρ εc M chart W d' β k')
      (∑ n ∈ Finset.Icc d' M, c⁻¹ * εc ^ n *
        (2 * (2 ^ Kt * ((Kt : ℝ) + 1) * D * Kc) * A n * (ρ ^ n * Rχ⁻¹ ^ (n - d')))) := by
  have hord : ∀ n ∈ Finset.Icc d' M, ScaledJet Kt Rχ
      (fun y => (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart y k' l •
        kernelTerm ρ chart W (d' - 1) β n l y)
      (c⁻¹ * εc ^ n *
        (2 * (2 ^ Kt * ((Kt : ℝ) + 1) * D * Kc) * A n * (ρ ^ n * Rχ⁻¹ ^ (n - d')))) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    refine scaledJet_mono (scaledJet_kernelOrder hc hε hR n hJ (fun l => hT n hn1 hn2 l))
      (le_of_eq ?_)
    ring
  have e : labelKernel c ρ εc M chart W d' β k' = fun y => ∑ n ∈ Finset.Icc d' M,
      (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart y k' l •
        kernelTerm ρ chart W (d' - 1) β n l y := rfl
  rw [e]
  exact scaledJet_sum (Finset.Icc d' M) hR.le hord

/-- Scale-weighted jets of the kernel of one pulse, with an amplitude `A n` for the letters of
each order `n` (the higher diagonal means cost `C ε_c^{n-2}`). -/
theorem pulseKernel_scaledJet_weighted (M Kt : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
      (c ρ εc Rχ lam : ℝ) (A : ℕ → ℝ) (chart label : Vec 2 → Vec 2)
      (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G),
      0 < c → 0 < ρ → 0 ≤ εc → 0 < Rχ → lam = ρ / Rχ → (∀ n, 0 ≤ A n) →
      ContDiff ℝ (⊤ : ℕ∞) chart → ContDiff ℝ (⊤ : ℕ∞) label →
      ChartTransport.JetBound chart (Kt + M) D Rχ → ChartTransport.JetBound label (Kt + M) D Rχ →
      (∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2),
        ContDiff ℝ (Kt : ℕ∞) (W n d α l)) →
      (∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2),
        ∀ i, i ≤ Kt → ∀ X, ‖iteratedFDeriv ℝ i (W n d α l) X‖ ≤ A n * lam ^ (n - d + i)) →
      ∀ d', 2 ≤ d' → d' ≤ M → ∀ (β : DerivativeWord2 (d' - 1)) (k' : Fin 2),
        ScaledJet Kt Rχ (pulseKernel c ρ εc M chart label W (d' - 1) β k')
          (C * ∑ n ∈ Finset.Icc d' M, A n * (c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n - d'))) := by
  obtain ⟨Cp, hCp0, hCp⟩ := chainCoeff_scaledJet_uniform D hD M Kt
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  refine ⟨(Kt.factorial : ℝ) * D ^ Kt * ((Kt : ℝ) + 1) *
    (2 * (2 ^ Kt * ((Kt : ℝ) + 1) * D * ((M : ℝ) * (2 ^ M * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp))))),
    by positivity, ?_⟩
  intro G _ _ c ρ εc Rχ lam A chart label W hc hρ hε hR hlam hA hchart hlabel hJc hJl hW hWb
    d' hd' hd'M β k'
  have hP := hCp chart Rχ hR hchart hJc
  have hJac : ∀ l : Fin 2, ScaledJet Kt Rχ (fun y => jacMatrix chart y k' l) D := fun l =>
    ⟨contDiff_natCast_of_top (contDiff_jacMatrix hchart k' l) Kt, fun y q hq =>
      jacMatrix_scaled_bound hR hchart hJc k' l y q (by omega)⟩
  have hlab : ChartTransport.JetBound label Kt D Rχ := by
    intro p hp1 hp y
    exact hJl p hp1 (by omega) y
  have hQ := scaledJet_labelKernel hc hε hR ρ M W β k' A
    ((M : ℝ) * (2 ^ M * (2 ^ Kt * ((Kt : ℝ) + 1) * Cp))) hJac
    (fun n hn hnM l => scaledJet_kernelTerm hρ hR hlam (hA n) hCp0 hchart hP hd' β hn hnM
      (fun d hd hdn α l' => hW n (hd'.trans hn) hnM d hd hdn α l')
      (fun d hd hdn α l' => hWb n (hd'.trans hn) hnM d hd hdn α l') l)
  have hcomp := scaledJet_comp hD hR hQ (contDiff_natCast_of_top hlabel Kt) hlab
  have e : pulseKernel c ρ εc M chart label W (d' - 1) β k' =
      fun x => labelKernel c ρ εc M chart W d' β k' (label x) :=
    funext fun x => pulseKernel_eq_labelKernel c ρ εc M chart label W hd' β k' x
  rw [e]
  refine scaledJet_mono hcomp (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_pow]
  ring

/-- Jets of the kernel of one pulse, with an amplitude `A n` for the letters of each order. -/
theorem pulseKernel_jet_bound_weighted (M Kt : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
      (c ρ εc Rχ lam : ℝ) (A : ℕ → ℝ) (chart label : Vec 2 → Vec 2)
      (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G),
      0 < c → 0 < ρ → 0 ≤ εc → 0 < Rχ → lam = ρ / Rχ → (∀ n, 0 ≤ A n) →
      ContDiff ℝ (⊤ : ℕ∞) chart → ContDiff ℝ (⊤ : ℕ∞) label →
      ChartTransport.JetBound chart (Kt + M) D Rχ → ChartTransport.JetBound label (Kt + M) D Rχ →
      (∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2),
        ContDiff ℝ (Kt : ℕ∞) (W n d α l)) →
      (∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2),
        ∀ i, i ≤ Kt → ∀ X, ‖iteratedFDeriv ℝ i (W n d α l) X‖ ≤ A n * lam ^ (n - d + i)) →
      ∀ d', 2 ≤ d' → d' ≤ M → ∀ (β : DerivativeWord2 (d' - 1)) (k' : Fin 2) (j : ℕ), j ≤ Kt →
        ∀ x, ‖iteratedFDeriv ℝ j (pulseKernel c ρ εc M chart label W (d' - 1) β k') x‖ ≤
          C * ∑ n ∈ Finset.Icc d' M, A n * (c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d')) := by
  obtain ⟨C, hC, hs⟩ := pulseKernel_scaledJet_weighted M Kt D hD
  refine ⟨C, hC, ?_⟩
  intro G _ _ c ρ εc Rχ lam A chart label W hc hρ hε hR hlam hA hchart hlabel hJc hJl hW hWb
    d' hd' hd'M β k' j hj x
  have h := (hs c ρ εc Rχ lam A chart label W hc hρ hε hR hlam hA hchart hlabel hJc hJl hW hWb
    d' hd' hd'M β k').bound x j hj
  refine (le_mul_inv_pow_of_scaled_le hR h).trans (le_of_eq ?_)
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : d' ≤ n := (Finset.mem_Icc.1 hn).1
  have e : n + j - d' = n - d' + j := by omega
  rw [e, pow_add]
  ring

/-- Jets of the kernel of one pulse. -/
theorem pulseKernel_jet_bound (M Kt : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
      (c ρ εc Rχ lam A : ℝ) (chart label : Vec 2 → Vec 2)
      (W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G),
      0 < c → 0 < ρ → 0 ≤ εc → 0 < Rχ → lam = ρ / Rχ → 0 ≤ A →
      ContDiff ℝ (⊤ : ℕ∞) chart → ContDiff ℝ (⊤ : ℕ∞) label →
      ChartTransport.JetBound chart (Kt + M) D Rχ → ChartTransport.JetBound label (Kt + M) D Rχ →
      (∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2),
        ContDiff ℝ (Kt : ℕ∞) (W n d α l)) →
      (∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2),
        ∀ i, i ≤ Kt → ∀ X, ‖iteratedFDeriv ℝ i (W n d α l) X‖ ≤ A * lam ^ (n - d + i)) →
      ∀ d', 2 ≤ d' → d' ≤ M → ∀ (β : DerivativeWord2 (d' - 1)) (k' : Fin 2) (j : ℕ), j ≤ Kt →
        ∀ x, ‖iteratedFDeriv ℝ j (pulseKernel c ρ εc M chart label W (d' - 1) β k') x‖ ≤
          C * A * ∑ n ∈ Finset.Icc d' M, c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d') := by
  obtain ⟨C, hC, hw⟩ := pulseKernel_jet_bound_weighted M Kt D hD
  refine ⟨C, hC, ?_⟩
  intro G _ _ c ρ εc Rχ lam A chart label W hc hρ hε hR hlam hA hchart hlabel hJc hJl hW hWb
    d' hd' hd'M β k' j hj x
  refine (hw c ρ εc Rχ lam (fun _ => A) chart label W hc hρ hε hR hlam (fun _ => hA) hchart
    hlabel hJc hJl hW hWb d' hd' hd'M β k' j hj x).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, mul_assoc]

end AVRegularity.CycleComparison.ActualMeans
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.CycleComparison.ActualMeans

/-! Regularity of the Eulerian kernels of the actual means: the pulse kernel is as smooth as its
letters and `ℤ²`-periodic for a lattice-equivariant chart; the windowed letters inherit smoothness,
periodicity and slow jets from the letters on the lift window; the glued kernel is jointly
measurable in time and position. -/

/-! ### Lambda forms of pointfree calculus lemmas -/

section Lambda

/-- The lambda form of `ContDiff.smul`. -/
theorem contDiff_smul_fun {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {n : WithTop ℕ∞} {f : E → ℝ} {g : E → G}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) : ContDiff ℝ n (fun x => f x • g x) :=
  hf.smul hg

/-- The lambda form of `Measurable.smul`. -/
theorem measurable_smul_fun {α G : Type*} [MeasurableSpace α] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G] {f : α → ℝ} {g : α → G}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => f x • g x) :=
  hf.smul hg

/-- The lambda form of `Measurable.const_smul`. -/
theorem measurable_const_smul_fun {α G : Type*} [MeasurableSpace α] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G] {g : α → G}
    (hg : Measurable g) (a : ℝ) : Measurable (fun x => a • g x) :=
  hg.const_smul a

end Lambda

/-! ### Lattice shifts of the chart coefficients -/

section Shift

/-- The derivative of a shift-invariant map is shift-invariant. -/
theorem fderiv_of_shift_invariant {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Vec 2 → F} (p : Vec 2) (hf : ∀ y, f (y + p) = f y) (y : Vec 2) :
    fderiv ℝ f (y + p) = fderiv ℝ f y := by
  have h1 : fderiv ℝ (fun z => f (z + p)) y = fderiv ℝ f (y + p) := fderiv_comp_add_right p
  have h2 : (fun z => f (z + p)) = f := funext hf
  rw [← h1, h2]

/-- The derivative of a shift-equivariant chart is shift-invariant. -/
theorem fderiv_of_shift_equivariant {Φ : Vec 2 → Vec 2} (p : Vec 2)
    (hΦ : ∀ y, Φ (y + p) = Φ y + p) (y : Vec 2) : fderiv ℝ Φ (y + p) = fderiv ℝ Φ y := by
  have h1 : fderiv ℝ (fun z => Φ (z + p)) y = fderiv ℝ Φ (y + p) := fderiv_comp_add_right p
  have h2 : (fun z => Φ (z + p)) = fun z => Φ z + p := funext hΦ
  rw [← h1, h2, fderiv_add_const]

/-- The Jacobian of a shift-equivariant chart is shift-invariant. -/
theorem jacMatrix_shift {Φ : Vec 2 → Vec 2} (p : Vec 2) (hΦ : ∀ y, Φ (y + p) = Φ y + p)
    (y : Vec 2) : jacMatrix Φ (y + p) = jacMatrix Φ y := by
  unfold jacMatrix
  rw [fderiv_of_shift_equivariant p hΦ y]

/-- The chain-rule coefficients of a shift-equivariant chart are shift-invariant. -/
theorem chainCoeff_shift {Φ : Vec 2 → Vec 2} (p : Vec 2) (hΦ : ∀ y, Φ (y + p) = Φ y + p) :
    ∀ (m : ℕ) (α : DerivativeWord2 m) (m' : ℕ) (β : DerivativeWord2 m') (y : Vec 2),
      chainCoeff Φ m α m' β (y + p) = chainCoeff Φ m α m' β y := by
  intro m
  induction m with
  | zero =>
    intro α m' β y
    simp only [chainCoeff_zero]
  | succ m ih =>
    intro α m' β y
    cases m' with
    | zero =>
      rw [chainCoeff_succ_zero]
      show fderiv ℝ (chainCoeff Φ m (fun i => α i.castSucc) 0 β) (y + p)
          (basisVec (α (Fin.last m))) =
        fderiv ℝ (chainCoeff Φ m (fun i => α i.castSucc) 0 β) y (basisVec (α (Fin.last m)))
      rw [fderiv_of_shift_invariant p (ih (fun i => α i.castSucc) 0 β) y]
    | succ m' =>
      rw [chainCoeff_succ_succ]
      show fderiv ℝ (chainCoeff Φ m (fun i => α i.castSucc) (m' + 1) β) (y + p)
            (basisVec (α (Fin.last m))) +
          chainCoeff Φ m (fun i => α i.castSucc) m' (fun i => β i.castSucc) (y + p) *
            jacMatrix Φ (y + p) (β (Fin.last m')) (α (Fin.last m)) =
        fderiv ℝ (chainCoeff Φ m (fun i => α i.castSucc) (m' + 1) β) y
            (basisVec (α (Fin.last m))) +
          chainCoeff Φ m (fun i => α i.castSucc) m' (fun i => β i.castSucc) y *
            jacMatrix Φ y (β (Fin.last m')) (α (Fin.last m))
      rw [fderiv_of_shift_invariant p (ih (fun i => α i.castSucc) (m' + 1) β) y,
        ih (fun i => α i.castSucc) m' (fun i => β i.castSucc) y, jacMatrix_shift p hΦ y]

end Shift

/-! ### The letter cut off to the lift window -/

section Cut

variable {G : Type*} [Zero G]

/-- The letter cut off to the lift window `[s₀, s₁]`, without the partition weight. -/
def cutLetter (s₀ s₁ : ℝ) (L : ℝ → Vec 2 → G) (s : ℝ) (X : Vec 2) : G :=
  open Classical in if s ∈ Set.Icc s₀ s₁ then L s X else 0

theorem cutLetter_of_mem {s₀ s₁ : ℝ} (L : ℝ → Vec 2 → G) {s : ℝ} (hs : s ∈ Set.Icc s₀ s₁)
    (X : Vec 2) : cutLetter s₀ s₁ L s X = L s X := by
  simp only [cutLetter, ite_eq_left hs]

theorem cutLetter_of_notMem {s₀ s₁ : ℝ} (L : ℝ → Vec 2 → G) {s : ℝ} (hs : s ∉ Set.Icc s₀ s₁)
    (X : Vec 2) : cutLetter s₀ s₁ L s X = 0 := by
  simp only [cutLetter, ite_eq_right hs]

end Cut

/-- The cut-off letter is jointly measurable when the letter is measurable in time on the window
and continuous in the slow variable there. -/
theorem measurable_cutLetter {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [BorelSpace G] (s₀ s₁ : ℝ) (L : ℝ → Vec 2 → G)
    (hLm : ∀ X : Vec 2, Measurable (fun s : Set.Icc s₀ s₁ => L s X))
    (hLc : ∀ s ∈ Set.Icc s₀ s₁, Continuous (L s)) :
    Measurable (fun q : ℝ × Vec 2 => cutLetter s₀ s₁ L q.1 q.2) := by
  have hcont : ∀ s : ℝ, Continuous (fun X : Vec 2 => cutLetter s₀ s₁ L s X) := by
    intro s
    by_cases hs : s ∈ Set.Icc s₀ s₁
    · have he : (fun X : Vec 2 => cutLetter s₀ s₁ L s X) = L s :=
        funext fun X => cutLetter_of_mem L hs X
      rw [he]
      exact hLc s hs
    · have he : (fun X : Vec 2 => cutLetter s₀ s₁ L s X) = fun _ => (0 : G) :=
        funext fun X => cutLetter_of_notMem L hs X
      rw [he]
      exact continuous_const
  have hmeas : ∀ X : Vec 2, Measurable (fun s : ℝ => cutLetter s₀ s₁ L s X) := by
    intro X
    refine measurable_of_restrict_of_restrict_compl
      (s := Set.Icc s₀ s₁) measurableSet_Icc ?_ ?_
    · show Measurable (fun s : Set.Icc s₀ s₁ => cutLetter s₀ s₁ L s X)
      have he : (fun s : Set.Icc s₀ s₁ => cutLetter s₀ s₁ L s X) =
          fun s : Set.Icc s₀ s₁ => L s X :=
        funext fun s => cutLetter_of_mem L s.2 X
      rw [he]
      exact hLm X
    · show Measurable (fun s : ((Set.Icc s₀ s₁)ᶜ : Set ℝ) => cutLetter s₀ s₁ L s X)
      have he : (fun s : ((Set.Icc s₀ s₁)ᶜ : Set ℝ) => cutLetter s₀ s₁ L s X) =
          fun _ => (0 : G) :=
        funext fun s => cutLetter_of_notMem L (show (s : ℝ) ∉ Set.Icc s₀ s₁ from s.2) X
      rw [he]
      exact measurable_const
  have hu : Measurable (Function.uncurry fun (X : Vec 2) (s : ℝ) => cutLetter s₀ s₁ L s X) :=
    measurable_uncurry_of_continuous_of_measurable
      (u := fun (X : Vec 2) (s : ℝ) => cutLetter s₀ s₁ L s X) hcont hmeas
  exact hu.comp measurable_swap

section Generic

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The windowed letter is the partition weight times the cut-off letter. -/
theorem windowLetter_eq_smul_cutLetter (ϖ : ℝ → ℝ) (c s₀ s₁ : ℝ) (L : ℝ → Vec 2 → G) (t : ℝ)
    (X : Vec 2) :
    windowLetter ϖ c s₀ s₁ L t X = ϖ t • cutLetter s₀ s₁ L (c⁻¹ * t) X := by
  by_cases ht : c⁻¹ * t ∈ Set.Icc s₀ s₁
  · rw [windowLetter_of_mem L ht X, cutLetter_of_mem L ht X]
  · rw [windowLetter_of_notMem L ht X, cutLetter_of_notMem L ht X, smul_zero]

/-- The windowed letter is as smooth as the letters on the window. -/
theorem contDiff_windowLetter (ϖ : ℝ → ℝ) (c s₀ s₁ : ℝ) (L : ℝ → Vec 2 → G) (t : ℝ)
    (n : ℕ∞) (hL : ∀ s ∈ Set.Icc s₀ s₁, ContDiff ℝ n (L s)) :
    ContDiff ℝ n (windowLetter ϖ c s₀ s₁ L t) := by
  by_cases ht : c⁻¹ * t ∈ Set.Icc s₀ s₁
  · have he : windowLetter ϖ c s₀ s₁ L t = fun X => ϖ t • L (c⁻¹ * t) X :=
      funext fun X => windowLetter_of_mem L ht X
    rw [he]
    exact ContDiff.const_smul (ϖ t) (hL (c⁻¹ * t) ht)
  · have he : windowLetter ϖ c s₀ s₁ L t = fun _ => (0 : G) :=
      funext fun X => windowLetter_of_notMem L ht X
    rw [he]
    exact contDiff_const

/-- The windowed letter inherits the periods of the letters on the window. -/
theorem windowLetter_periodic (ϖ : ℝ → ℝ) (c s₀ s₁ : ℝ) (L : ℝ → Vec 2 → G) (t : ℝ)
    (T X : Vec 2) (hL : ∀ s ∈ Set.Icc s₀ s₁, L s (X + T) = L s X) :
    windowLetter ϖ c s₀ s₁ L t (X + T) = windowLetter ϖ c s₀ s₁ L t X := by
  by_cases ht : c⁻¹ * t ∈ Set.Icc s₀ s₁
  · rw [windowLetter_of_mem L ht (X + T), windowLetter_of_mem L ht X, hL (c⁻¹ * t) ht]
  · rw [windowLetter_of_notMem L ht (X + T), windowLetter_of_notMem L ht X]

/-- Iterated derivatives of a constant multiple, with no smoothness assumption. -/
theorem norm_iteratedFDeriv_const_smul_le (a : ℝ) (f : Vec 2 → G) (i : ℕ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ i (fun Y => a • f Y) X‖ ≤ |a| * ‖iteratedFDeriv ℝ i f X‖ := by
  by_cases ha : a = 0
  · have he : (fun Y : Vec 2 => a • f Y) = fun _ => (0 : G) := by
      funext Y
      rw [ha, zero_smul]
    have h0 : iteratedFDeriv ℝ i (fun Y : Vec 2 => a • f Y) X = 0 := by
      rw [he]
      exact congrFun iteratedFDeriv_fun_zero X
    rw [h0, norm_zero]
    exact mul_nonneg (abs_nonneg a) (norm_nonneg _)
  · obtain ⟨g, hg⟩ : ∃ g : G ≃L[ℝ] G, ∀ y, g y = a • y :=
      ⟨ContinuousLinearEquiv.equivOfInverse (a • ContinuousLinearMap.id ℝ G)
        (a⁻¹ • ContinuousLinearMap.id ℝ G) (fun y => inv_smul_smul₀ ha y)
        (fun y => smul_inv_smul₀ ha y), fun y => rfl⟩
    have hfun : (fun Y : Vec 2 => a • f Y) = (g : G → G) ∘ f :=
      funext fun Y => (hg (f Y)).symm
    have hder := g.iteratedFDeriv_comp_left (f := f) (x := X) (i := i)
    have hnorm : ‖g.toContinuousLinearMap‖ ≤ |a| := by
      refine ContinuousLinearMap.opNorm_le_bound g.toContinuousLinearMap (abs_nonneg a)
        fun y => ?_
      have hy : ‖g y‖ = |a| * ‖y‖ := by rw [hg y, norm_smul, Real.norm_eq_abs]
      exact hy.le
    rw [hfun, hder]
    exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le g.toContinuousLinearMap
      (iteratedFDeriv ℝ i f X)).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

/-- Slow jets of the windowed letter. -/
theorem norm_iteratedFDeriv_windowLetter_le (ϖ : ℝ → ℝ) (c s₀ s₁ : ℝ) (L : ℝ → Vec 2 → G)
    (t : ℝ) (i : ℕ) (X : Vec 2) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ s ∈ Set.Icc s₀ s₁, ‖iteratedFDeriv ℝ i (L s) X‖ ≤ B) :
    ‖iteratedFDeriv ℝ i (windowLetter ϖ c s₀ s₁ L t) X‖ ≤ |ϖ t| * B := by
  by_cases ht : c⁻¹ * t ∈ Set.Icc s₀ s₁
  · have he : windowLetter ϖ c s₀ s₁ L t = fun Y => ϖ t • L (c⁻¹ * t) Y :=
      funext fun Y => windowLetter_of_mem L ht Y
    rw [he]
    exact (norm_iteratedFDeriv_const_smul_le (ϖ t) (L (c⁻¹ * t)) i X).trans
      (mul_le_mul_of_nonneg_left (hL (c⁻¹ * t) ht) (abs_nonneg _))
  · have he : windowLetter ϖ c s₀ s₁ L t = fun _ => (0 : G) :=
      funext fun Y => windowLetter_of_notMem L ht Y
    have h0 : iteratedFDeriv ℝ i (windowLetter ϖ c s₀ s₁ L t) X = 0 := by
      rw [he]
      exact congrFun iteratedFDeriv_fun_zero X
    rw [h0, norm_zero]
    exact mul_nonneg (abs_nonneg _) hB

/-- The pulse kernel is as smooth as its letters. -/
theorem contDiff_pulseKernel (c ρ εc : ℝ) (M Kt : ℕ) {chart label : Vec 2 → Vec 2}
    (hchart : ContDiff ℝ (⊤ : ℕ∞) chart) (hlabel : ContDiff ℝ (⊤ : ℕ∞) label)
    {W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G}
    (hW : ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2),
      ContDiff ℝ (Kt : ℕ∞) (W n d α l))
    (m' : ℕ) (β : DerivativeWord2 m') (k' : Fin 2) :
    ContDiff ℝ (Kt : ℕ∞) (pulseKernel c ρ εc M chart label W m' β k') := by
  have htop : ((Kt : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hJ (l : Fin 2) : ContDiff ℝ (Kt : ℕ∞) (fun x => jacMatrix chart (label x) k' l) :=
    ((contDiff_jacMatrix hchart k' l).comp hlabel).of_le htop
  have hP (d : ℕ) (α : DerivativeWord2 (d - 1)) :
      ContDiff ℝ (Kt : ℕ∞) (fun x => chainCoeff chart (d - 1) α m' β (label x)) :=
    ((contDiff_chainCoeff hchart (d - 1) α m' β).comp hlabel).of_le htop
  have hX : ContDiff ℝ (Kt : ℕ∞) (fun x => ρ⁻¹ • label x) :=
    ((contDiff_const_smul ρ⁻¹).comp hlabel).of_le htop
  have hterm : ∀ n ∈ Finset.Icc 2 M, ∀ l : Fin 2, ∀ d ∈ Finset.Icc 2 n,
      ∀ α : DerivativeWord2 (d - 1), ContDiff ℝ (Kt : ℕ∞)
        (fun x => chainCoeff chart (d - 1) α m' β (label x) • W n d α l (ρ⁻¹ • label x)) := by
    intro n hn l d hd α
    have hn' := Finset.mem_Icc.mp hn
    have hd' := Finset.mem_Icc.mp hd
    exact contDiff_smul_fun (hP d α) ((hW n hn'.1 hn'.2 d hd'.1 hd'.2 α l).comp hX)
  have hdsum : ∀ n ∈ Finset.Icc 2 M, ∀ l : Fin 2, ∀ d ∈ Finset.Icc 2 n,
      ContDiff ℝ (Kt : ℕ∞) (fun x => ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
        chainCoeff chart (d - 1) α m' β (label x) • W n d α l (ρ⁻¹ • label x)) :=
    fun n hn l d hd => ContDiff.const_smul (ρ ^ d) (ContDiff.sum fun α _ => hterm n hn l d hd α)
  have hlsum : ∀ n ∈ Finset.Icc 2 M, ∀ l : Fin 2,
      ContDiff ℝ (Kt : ℕ∞) (fun x => jacMatrix chart (label x) k' l •
        ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
          chainCoeff chart (d - 1) α m' β (label x) • W n d α l (ρ⁻¹ • label x)) :=
    fun n hn l => contDiff_smul_fun (hJ l) (ContDiff.sum fun d hd => hdsum n hn l d hd)
  have hnsum : ∀ n ∈ Finset.Icc 2 M,
      ContDiff ℝ (Kt : ℕ∞) (fun x => (c⁻¹ * εc ^ n) • ∑ l : Fin 2,
        jacMatrix chart (label x) k' l •
          ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
            chainCoeff chart (d - 1) α m' β (label x) • W n d α l (ρ⁻¹ • label x)) :=
    fun n hn => ContDiff.const_smul (c⁻¹ * εc ^ n) (ContDiff.sum fun l _ => hlsum n hn l)
  show ContDiff ℝ (Kt : ℕ∞) (fun x => ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2,
    jacMatrix chart (label x) k' l •
      ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
        chainCoeff chart (d - 1) α m' β (label x) • W n d α l (ρ⁻¹ • label x))
  exact ContDiff.sum hnsum

/-- The pulse kernel of a lattice-equivariant chart is `ℤ²`-periodic. -/
theorem isZ2Periodic_pulseKernel (c ρ εc : ℝ) (M : ℕ) {chart label : Vec 2 → Vec 2}
    (hchart : ∀ (p : Fin 2 → ℤ) (y : Vec 2),
      chart (y + AVenhance.latticeShift p) = chart y + AVenhance.latticeShift p)
    (hlabel : ∀ (p : Fin 2 → ℤ) (x : Vec 2),
      label (x + AVenhance.latticeShift p) = label x + AVenhance.latticeShift p)
    {W : (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Vec 2 → G}
    (hW : ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2)
      (p : Fin 2 → ℤ) (X : Vec 2), W n d α l (X + ρ⁻¹ • AVenhance.latticeShift p) = W n d α l X)
    (m' : ℕ) (β : DerivativeWord2 m') (k' : Fin 2) :
    AVenhance.IsZ2Periodic (pulseKernel c ρ εc M chart label W m' β k') := by
  intro p x
  simp only [pulseKernel, hlabel p x]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_Icc.mp hn
  refine congrArg (fun z : G => (c⁻¹ * εc ^ n) • z) ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [jacMatrix_shift (AVenhance.latticeShift p) (hchart p) (label x)]
  refine congrArg (fun z : G => jacMatrix chart (label x) k' l • z) ?_
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' := Finset.mem_Icc.mp hd
  refine congrArg (fun z : G => ρ ^ d • z) ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [chainCoeff_shift (AVenhance.latticeShift p) (hchart p) (d - 1) α m' β (label x),
    smul_add, hW n hn'.1 hn'.2 d hd'.1 hd'.2 α l p (ρ⁻¹ • label x)]

end Generic

/-- The windowed letter, read at the slow label of the position, is jointly measurable in time
and position. -/
theorem measurable_windowLetter_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] (ϖ : ℝ → ℝ) (c ρ s₀ s₁ : ℝ) (L : ℝ → Vec 2 → G)
    (label : ℝ → Vec 2 → Vec 2) (hϖ : Measurable ϖ)
    (hlabel : Measurable (fun q : ℝ × Vec 2 => label q.1 q.2))
    (hLm : ∀ X : Vec 2, Measurable (fun s : Set.Icc s₀ s₁ => L s X))
    (hLc : ∀ s ∈ Set.Icc s₀ s₁, Continuous (L s)) :
    Measurable (fun q : ℝ × Vec 2 => windowLetter ϖ c s₀ s₁ L q.1 (ρ⁻¹ • label q.1 q.2)) := by
  have he : (fun q : ℝ × Vec 2 => windowLetter ϖ c s₀ s₁ L q.1 (ρ⁻¹ • label q.1 q.2)) =
      fun q => ϖ q.1 • cutLetter s₀ s₁ L (c⁻¹ * q.1) (ρ⁻¹ • label q.1 q.2) :=
    funext fun q => windowLetter_eq_smul_cutLetter ϖ c s₀ s₁ L q.1 (ρ⁻¹ • label q.1 q.2)
  rw [he]
  have hslow : Measurable (fun q : ℝ × Vec 2 => ρ⁻¹ • label q.1 q.2) :=
    hlabel.const_smul ρ⁻¹
  have hpair : Measurable (fun q : ℝ × Vec 2 => (c⁻¹ * q.1, ρ⁻¹ • label q.1 q.2)) :=
    (measurable_fst.const_mul c⁻¹).prodMk hslow
  have hcut : Measurable
      (fun q : ℝ × Vec 2 => cutLetter s₀ s₁ L (c⁻¹ * q.1) (ρ⁻¹ • label q.1 q.2)) :=
    (measurable_cutLetter s₀ s₁ L hLm hLc).comp hpair
  have hw : Measurable (fun q : ℝ × Vec 2 => ϖ q.1) := hϖ.comp measurable_fst
  exact measurable_smul_fun hw hcut

/-- The glued kernel is jointly measurable in time and position. -/
theorem measurable_gluedKernel {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
    (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (M : ℕ)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (L : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → G)
    (hϖ : ∀ k ∈ kset, Measurable (ϖ k))
    (hchart : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => chart k q.1 q.2))
    (hlabel : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => label k q.1 q.2))
    (hLm : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2) (X : Vec 2),
        Measurable (fun s : Set.Icc (s₀ k) (s₁ k) => L k n d α l s X))
    (hLc : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        Continuous (L k n d α l s))
    (m' : ℕ) (β : DerivativeWord2 m') (k' : Fin 2) :
    Measurable (fun q : ℝ × Vec 2 =>
      gluedKernel kset ϖ c ρ εc M chart label s₀ s₁ L m' β k' q.1 q.2) := by
  have hlab : ∀ k ∈ kset, Measurable (fun q : ℝ × Vec 2 => label k q.1 q.2) :=
    fun k hk => (hlabel k hk).continuous.measurable
  have hJ : ∀ k ∈ kset, ∀ l : Fin 2,
      Measurable (fun q : ℝ × Vec 2 => jacMatrix (chart k q.1) (label k q.1 q.2) k' l) :=
    fun k hk l => ((contDiff_jacMatrix_joint (Φ := chart k) (hchart k hk) k' l).comp
      (contDiff_fst.prodMk (hlabel k hk))).continuous.measurable
  have hP : ∀ k ∈ kset, ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)),
      Measurable (fun q : ℝ × Vec 2 =>
        chainCoeff (chart k q.1) (d - 1) α m' β (label k q.1 q.2)) :=
    fun k hk d α => ((contDiff_chainCoeff_joint (Φ := chart k) (hchart k hk) (d - 1) α m' β).comp
      (contDiff_fst.prodMk (hlabel k hk))).continuous.measurable
  have hterm : ∀ k ∈ kset, ∀ n ∈ Finset.Icc 2 M, ∀ l : Fin 2, ∀ d ∈ Finset.Icc 2 n,
      ∀ α : DerivativeWord2 (d - 1), Measurable (fun q : ℝ × Vec 2 =>
        chainCoeff (chart k q.1) (d - 1) α m' β (label k q.1 q.2) •
          windowLetter (ϖ k) c (s₀ k) (s₁ k) (L k n d α l) q.1 (ρ⁻¹ • label k q.1 q.2)) := by
    intro k hk n hn l d hd α
    have hn' := Finset.mem_Icc.mp hn
    have hd' := Finset.mem_Icc.mp hd
    exact measurable_smul_fun (hP k hk d α)
      (measurable_windowLetter_comp (ϖ k) c ρ (s₀ k) (s₁ k) (L k n d α l) (label k)
        (hϖ k hk) (hlab k hk) (hLm k hk n hn'.1 hn'.2 d hd'.1 hd'.2 α l)
        (hLc k hk n hn'.1 hn'.2 d hd'.1 hd'.2 α l))
  have hdsum : ∀ k ∈ kset, ∀ n ∈ Finset.Icc 2 M, ∀ l : Fin 2, ∀ d ∈ Finset.Icc 2 n,
      Measurable (fun q : ℝ × Vec 2 => ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
        chainCoeff (chart k q.1) (d - 1) α m' β (label k q.1 q.2) •
          windowLetter (ϖ k) c (s₀ k) (s₁ k) (L k n d α l) q.1 (ρ⁻¹ • label k q.1 q.2)) :=
    fun k hk n hn l d hd => measurable_const_smul_fun
      (Finset.measurable_sum Finset.univ fun α _ => hterm k hk n hn l d hd α) (ρ ^ d)
  have hlsum : ∀ k ∈ kset, ∀ n ∈ Finset.Icc 2 M, ∀ l : Fin 2,
      Measurable (fun q : ℝ × Vec 2 => jacMatrix (chart k q.1) (label k q.1 q.2) k' l •
        ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
          chainCoeff (chart k q.1) (d - 1) α m' β (label k q.1 q.2) •
            windowLetter (ϖ k) c (s₀ k) (s₁ k) (L k n d α l) q.1 (ρ⁻¹ • label k q.1 q.2)) :=
    fun k hk n hn l => measurable_smul_fun (hJ k hk l)
      (Finset.measurable_sum (Finset.Icc 2 n) fun d hd => hdsum k hk n hn l d hd)
  have hnsum : ∀ k ∈ kset, ∀ n ∈ Finset.Icc 2 M,
      Measurable (fun q : ℝ × Vec 2 => (c⁻¹ * εc ^ n) • ∑ l : Fin 2,
        jacMatrix (chart k q.1) (label k q.1 q.2) k' l •
          ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
            chainCoeff (chart k q.1) (d - 1) α m' β (label k q.1 q.2) •
              windowLetter (ϖ k) c (s₀ k) (s₁ k) (L k n d α l) q.1
                (ρ⁻¹ • label k q.1 q.2)) :=
    fun k hk n hn => measurable_const_smul_fun
      (Finset.measurable_sum Finset.univ fun l _ => hlsum k hk n hn l) (c⁻¹ * εc ^ n)
  have hksum : ∀ k ∈ kset,
      Measurable (fun q : ℝ × Vec 2 => ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2,
        jacMatrix (chart k q.1) (label k q.1 q.2) k' l •
          ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
            chainCoeff (chart k q.1) (d - 1) α m' β (label k q.1 q.2) •
              windowLetter (ϖ k) c (s₀ k) (s₁ k) (L k n d α l) q.1
                (ρ⁻¹ • label k q.1 q.2)) :=
    fun k hk => Finset.measurable_sum (Finset.Icc 2 M) fun n hn => hnsum k hk n hn
  show Measurable (fun q : ℝ × Vec 2 => ∑ k ∈ kset, ∑ n ∈ Finset.Icc 2 M,
    (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix (chart k q.1) (label k q.1 q.2) k' l •
      ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1),
        chainCoeff (chart k q.1) (d - 1) α m' β (label k q.1 q.2) •
          windowLetter (ϖ k) c (s₀ k) (s₁ k) (L k n d α l) q.1 (ρ⁻¹ • label k q.1 q.2))
  exact Finset.measurable_sum kset hksum

end AVRegularity.CycleComparison.ActualMeans
end
