-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.Graded.Edges
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import AVRegularity.EntryWeak.MolecularHilbertToRawSolution

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the ledger of the transferred direct copies.** The real majorant `dirBound` of a
transferred direct copy of order `d` (`|C_d| Σ_{d₁,I₁,i₀} K W (|c_{d₁}| Σ_σ θ_old) c^{d₁-1}
ε_i^{-(d₁-d)}`) bounds its structural norm at every slot and time
(`genNorm_copyDir_le_dirBound`), given real bounds `K` of the inverse-transition entries on the fast
weights up to `D_m`, `W` of the child profile and `C_old` of the Cauchy constant, within the reserve
`mres + D_m Δ ≤ 2`. Its tagged size against the old record is at most
`2^{D_m}(D_m+1) K W c^{D_m}` times the old record size (`dirBound_record_le`), given `ℓ ≤ ε_i`,
`κ_{i+1} ≤ κ_i` and the old record bound. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

theorem sum_le_ofReal_sum {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞} {g : ι → ℝ}
    (hg : ∀ x ∈ s, 0 ≤ g x) (h : ∀ x ∈ s, f x ≤ ENNReal.ofReal (g x)) :
    ∑ x ∈ s, f x ≤ ENNReal.ofReal (∑ x ∈ s, g x) := by
  rw [ENNReal.ofReal_sum_of_nonneg hg]
  exact Finset.sum_le_sum h

theorem mul_le_ofReal_mul {a b : ℝ≥0∞} {x y : ℝ} (hx : 0 ≤ x) (ha : a ≤ ENNReal.ofReal x)
    (hb : b ≤ ENNReal.ofReal y) : a * b ≤ ENNReal.ofReal (x * y) := by
  rw [ENNReal.ofReal_mul hx]
  exact mul_le_mul' ha hb

/-- A component of the next family has at most the reserve of its old component. -/
theorem compReserve_succComp_le (k : InvConsts) (m : ℕ) (v : Comp) (t : List WordLetter) :
    compReserve k (succComp m v t) ≤ compReserve k v := by
  unfold succComp
  split_ifs
  · exact le_rfl
  · unfold compReserve compGrade
    simp only [List.length_cons]
    have : ((k.G0 + v.births.length : ℕ) : ℝ) ≤ ((k.G0 + (v.births.length + 1) : ℕ) : ℝ) := by
      exact_mod_cast (by omega)
    have hH : (0 : ℝ) < (k.Hprod : ℝ) + 1 := by positivity
    have := div_le_div_of_nonneg_right this hH.le
    linarith

/-- **The real majorant of a transferred direct copy** of order `d` at the coarse level `i`, from
the old level `m` with the old ledger entries `θo`. -/
def dirBound (D : OCData) (i m Dm Dγ : ℕ) (K W c lam : ℝ)
    (θo : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ) (d : ℕ) : ℝ :=
  |(D.kap i * D.eps i ^ (d - 2))⁻¹ * lam| *
    ∑ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ, ∑ I₁ : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2,
      K * W * (|directConst D m (Finset.Icc 3 Dm) d₁| *
        ∑ σ : Equiv.Perm (Fin (d₁ - 1)), θo d₁ (I₁ ∘ σ) i₀) *
        (c ^ (d₁ - 1) * (D.eps i)⁻¹ ^ (d₁ - 1 - (d - 1)))

theorem dirBound_nonneg (D : OCData) (i m Dm Dγ : ℕ) {K W c : ℝ} (lam : ℝ) (hK : 0 ≤ K)
    (hW : 0 ≤ W) (hc : 0 ≤ c) (hε : 0 ≤ D.eps i) {θo : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ}
    (hθo : ∀ d α c, 0 ≤ θo d α c) (d : ℕ) : 0 ≤ dirBound D i m Dm Dγ K W c lam θo d := by
  unfold dirBound
  refine mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun d₁ _ => Finset.sum_nonneg fun I₁ _ =>
    Finset.sum_nonneg fun i₀ _ => ?_)
  have : 0 ≤ ∑ σ : Equiv.Perm (Fin (d₁ - 1)), θo d₁ (I₁ ∘ σ) i₀ :=
    Finset.sum_nonneg fun σ _ => hθo _ _ _
  positivity

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts} {G : GenStage D hr Dm b j₀}

/-- **The transferred direct copy is bounded by its real majorant** at every slot and time. -/
theorem genNorm_copyDir_le_dirBound (κc : MajConsts) (Δ a₀ : ℝ)
    (hcert : G.OldCert G.exports (compReserve kI) kI.Lstar 1) (hb : 0 ≤ b) (hε : ∀ k, 0 ≤ D.eps k) {i : ℕ}
    (hlev : G.level = i + 1) (hτ : 0 < ocTau D.α D.q D.Λ (i + 1)) (hε0 : 0 < D.eps i)
    (hε1 : D.eps i ≤ 1) (hΔ : 0 < Δ) {v u : CompIn G.comps} (γ : G.fam.Γ v u) (lam : ℝ)
    (Dγ d : ℕ) (hDγ : Dγ ≤ Dm) (I : DerivativeWord2 (d - 1)) (c : Fin 2) (p : OddSlot) (a mres : ℝ)
    (t : ℝ) (hmres : mres ≤ compReserve kI v.1) (hres : mres + Dm * Δ ≤ 2)
    (ha₀ : a₀ ≤ 3 * Real.pi * b) {K W Cold : ℝ} (hK0 : 0 ≤ K) (hW0 : 0 ≤ W) (hC0 : 0 ≤ Cold)
    (hK : ∀ L, L ≤ Dm → kBound κc a L ≤ ENNReal.ofReal K)
    (hW : wsum a 0 κc.child ≤ ENNReal.ofReal W) (hCold : κc.Cold ≤ ENNReal.ofReal Cold) :
    genNorm D κc Δ a₀ (oldLeaf hcert)
        (transferExprAt D i lam Dγ d I c (cfinCopyDir hcert hlev γ) p) a mres 0 t ≤
      ENNReal.ofReal (dirBound D i G.level Dm Dγ K W (tConst K Cold Δ) lam
        (oldTheta hcert v u γ) d) := by
  refine (genNorm_transferExprAt_copyDir_le κc Δ a₀ hcert hb hε hlev hτ γ lam Dγ d I c p a mres 0
    t hmres ha₀).trans ?_
  have hθo := (oldTheta_spec hcert v u γ).1
  have hc0 := tConst_nonneg hK0 hC0 hΔ
  unfold dirBound
  refine mul_le_ofReal_mul (abs_nonneg _) le_rfl ?_
  refine sum_le_ofReal_sum (fun d₁ _ => Finset.sum_nonneg fun I₁ _ => Finset.sum_nonneg
    fun i₀ _ => ?_) fun d₁ hd₁ => sum_le_ofReal_sum (fun I₁ _ => Finset.sum_nonneg
    fun i₀ _ => ?_) fun I₁ _ => sum_le_ofReal_sum (fun i₀ _ => ?_) fun i₀ _ => ?_
  · have : 0 ≤ ∑ σ : Equiv.Perm (Fin (d₁ - 1)), oldTheta hcert v u γ d₁ (I₁ ∘ σ) i₀ :=
      Finset.sum_nonneg fun σ _ => hθo _ _ _
    positivity
  · have : 0 ≤ ∑ σ : Equiv.Perm (Fin (d₁ - 1)), oldTheta hcert v u γ d₁ (I₁ ∘ σ) i₀ :=
      Finset.sum_nonneg fun σ _ => hθo _ _ _
    positivity
  · have : 0 ≤ ∑ σ : Equiv.Perm (Fin (d₁ - 1)), oldTheta hcert v u γ d₁ (I₁ ∘ σ) i₀ :=
      Finset.sum_nonneg fun σ _ => hθo _ _ _
    positivity
  · have hσ : 0 ≤ ∑ σ : Equiv.Perm (Fin (d₁ - 1)), oldTheta hcert v u γ d₁ (I₁ ∘ σ) i₀ :=
      Finset.sum_nonneg fun σ _ => hθo _ _ _
    have hd₁' := Finset.mem_Icc.mp hd₁
    -- the Piola factor
    have hT := (tBound_le D κc hε0 hε1 hΔ hC0 hK0 hCold hK (d₁ - 1) (d - 1) mres 0
      (by
        have : ((d₁ - 1 : ℕ) : ℝ) * Δ ≤ Dm * Δ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : d₁ - 1 ≤ Dm)) hΔ.le
        linarith)
      (by omega)).2 (by omega)
    -- the old leaves
    have hO : ENNReal.ofReal |directConst D G.level (Finset.Icc 3 Dm) d₁| *
        ∑ σ : Equiv.Perm (Fin (d₁ - 1)), ENNReal.ofReal (oldTheta hcert v u γ d₁ (I₁ ∘ σ) i₀) =
        ENNReal.ofReal (|directConst D G.level (Finset.Icc 3 Dm) d₁| *
          ∑ σ : Equiv.Perm (Fin (d₁ - 1)), oldTheta hcert v u γ d₁ (I₁ ∘ σ) i₀) := by
      rw [ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_sum_of_nonneg fun σ _ => hθo _ _ _]
    rw [hO]
    refine mul_le_ofReal_mul (by positivity) ?_ hT
    refine mul_le_ofReal_mul (by positivity) ?_ le_rfl
    exact mul_le_ofReal_mul hK0 (hK 0 (Nat.zero_le _)) hW

/-- **One direct order of the majorant against the old record.** -/
theorem dirBound_term_le (D : OCData) (i Dm : ℕ) {K W c : ℝ} (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hc : 0 ≤ c) {θo : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ}
    (hθo : ∀ d α c, 0 ≤ θo d α c) {ℓ S : ℝ} (hℓ : 0 < ℓ) (hℓE : ℓ ≤ D.eps i) (hE : 0 < D.eps i)
    (he : 0 < D.eps (i + 1)) (hκ : 0 < D.kap i) (hκ' : 0 ≤ D.kap (i + 1))
    (hκκ : D.kap (i + 1) ≤ D.kap i) (hS : 0 ≤ S) (d d₁ : ℕ) (hd : 2 ≤ d) (hdd₁ : d ≤ d₁)
    (hold : (D.eps (i + 1) / ℓ) ^ (d₁ - 2) * ∑ J : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2,
      θo d₁ J i₀ ≤ S) :
    (D.eps i / ℓ) ^ (d - 2) * |(D.kap i * D.eps i ^ (d - 2))⁻¹ * 1| *
        ∑ I₁ : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2,
          K * W * (|directConst D (i + 1) (Finset.Icc 3 Dm) d₁| *
            ∑ σ : Equiv.Perm (Fin (d₁ - 1)), θo d₁ (I₁ ∘ σ) i₀) *
            (c ^ (d₁ - 1) * (D.eps i)⁻¹ ^ (d₁ - 1 - (d - 1))) ≤
      K * W * (c ^ (d₁ - 1) * S) := by
  have hsθ0 : 0 ≤ ∑ J : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2, θo d₁ J i₀ :=
    Finset.sum_nonneg fun J _ => Finset.sum_nonneg fun i₀ _ => hθo _ _ _
  have hsum : ∀ cd T : ℝ, ∑ I₁ : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2,
      K * W * (|cd| * ∑ σ : Equiv.Perm (Fin (d₁ - 1)), θo d₁ (I₁ ∘ σ) i₀) * T =
      K * W * |cd| * T * (((d₁ - 1).factorial : ℝ) *
        ∑ J : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2, θo d₁ J i₀) := by
    intro cd T
    calc ∑ I₁ : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2,
          K * W * (|cd| * ∑ σ : Equiv.Perm (Fin (d₁ - 1)), θo d₁ (I₁ ∘ σ) i₀) * T
        = ∑ I₁ : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2,
          K * W * |cd| * T * ∑ σ : Equiv.Perm (Fin (d₁ - 1)), θo d₁ (I₁ ∘ σ) i₀ :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = K * W * |cd| * T * ∑ I₁ : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2,
          ∑ σ : Equiv.Perm (Fin (d₁ - 1)), θo d₁ (I₁ ∘ σ) i₀ := by
          simp only [Finset.mul_sum]
      _ = _ := by rw [sum_perm_comp (d₁ - 1) (θo d₁)]
  rw [hsum]
  generalize (∑ J : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2, θo d₁ J i₀) = sθ at hold hsθ0 ⊢
  by_cases hmem : d₁ ∈ Finset.Icc 3 Dm
  · have hcd' : directConst D (i + 1) (Finset.Icc 3 Dm) d₁ =
        D.kap (i + 1) * D.eps (i + 1) ^ (d₁ - 2) * ((d₁ - 1).factorial : ℝ)⁻¹ := by
      unfold directConst
      simp only [hmem, ↓reduceIte]
    have hfac : (0 : ℝ) < (d₁ - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have habs : |directConst D (i + 1) (Finset.Icc 3 Dm) d₁| * ((d₁ - 1).factorial : ℝ) =
        D.kap (i + 1) * D.eps (i + 1) ^ (d₁ - 2) := by
      have hnn : 0 ≤ D.kap (i + 1) * D.eps (i + 1) ^ (d₁ - 2) * ((d₁ - 1).factorial : ℝ)⁻¹ := by
        positivity
      rw [hcd', abs_of_nonneg hnn, inv_mul_cancel_right₀ hfac.ne']
    have hkj : d₁ - 2 = (d - 2) + (d₁ - 1 - (d - 1)) := by omega
    have hold' : (D.eps (i + 1) / ℓ) ^ ((d - 2) + (d₁ - 1 - (d - 1))) * sθ ≤ S := by
      rw [← hkj]
      exact hold
    have key := dirTerm_le hE he hℓ hℓE hκ hκ' hκκ hc hsθ0 (d - 2) (d₁ - 1 - (d - 1)) (d₁ - 1)
      hold'
    rw [← hkj] at key
    calc (D.eps i / ℓ) ^ (d - 2) * |(D.kap i * D.eps i ^ (d - 2))⁻¹ * 1| *
          (K * W * |directConst D (i + 1) (Finset.Icc 3 Dm) d₁| *
            (c ^ (d₁ - 1) * (D.eps i)⁻¹ ^ (d₁ - 1 - (d - 1))) *
            (((d₁ - 1).factorial : ℝ) * sθ))
        = K * W * ((D.eps i / ℓ) ^ (d - 2) * |(D.kap i * D.eps i ^ (d - 2))⁻¹| *
            (D.kap (i + 1) * D.eps (i + 1) ^ (d₁ - 2) *
              (c ^ (d₁ - 1) * (D.eps i)⁻¹ ^ (d₁ - 1 - (d - 1))) * sθ)) := by
          rw [mul_one, ← habs]
          ring
      _ ≤ K * W * (c ^ (d₁ - 1) * S) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg hK hW)
  · have hcd0 : directConst D (i + 1) (Finset.Icc 3 Dm) d₁ = 0 := by
      unfold directConst
      simp only [hmem, ↓reduceIte]
    rw [hcd0, abs_zero, mul_zero, zero_mul, zero_mul, mul_zero]
    have : 0 ≤ c ^ (d₁ - 1) * S := by positivity
    positivity

/-- **The record bound of a transferred direct copy.** Its tagged size, summed over the words and
components of order `d`, is at most `2^{D_m}(D_m+1) W_r K W c^{D_m}` times the old record size. -/
theorem dirBound_record_le (D : OCData) (i Dm Dγ : ℕ) (hDγ : Dγ ≤ Dm) {K W c Wr : ℝ}
    (hK : 0 ≤ K) (hW : 0 ≤ W) (hc : 1 ≤ c) (hWr : 0 ≤ Wr)
    {θo : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ} (hθo : ∀ d α c, 0 ≤ θo d α c) {ℓ S : ℝ}
    (hℓ : 0 < ℓ) (hℓE : ℓ ≤ D.eps i) (hE : 0 < D.eps i) (he : 0 < D.eps (i + 1))
    (hκ : 0 < D.kap i) (hκ' : 0 ≤ D.kap (i + 1)) (hκκ : D.kap (i + 1) ≤ D.kap i) (hS : 0 ≤ S)
    (hold : ∀ d₁, 2 ≤ d₁ → d₁ ≤ Dγ → (D.eps (i + 1) / ℓ) ^ (d₁ - 2) *
      ∑ J : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2, θo d₁ J i₀ ≤ S)
    (d : ℕ) (hd : 2 ≤ d) (hdD : d ≤ Dγ) :
    (D.eps i / ℓ) ^ (d - 2) * ∑ _α : DerivativeWord2 (d - 1), ∑ _c' : Fin 2,
        Wr * dirBound D i (i + 1) Dm Dγ K W c 1 θo d ≤
      (2 ^ Dm * (Dm + 1) * Wr * K * W * c ^ Dm) * S := by
  have hc0 : 0 ≤ c := by linarith
  -- one order of the transfer
  have hterm : ∀ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ,
      (D.eps i / ℓ) ^ (d - 2) * |(D.kap i * D.eps i ^ (d - 2))⁻¹ * 1| *
        ∑ I₁ : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2,
          K * W * (|directConst D (i + 1) (Finset.Icc 3 Dm) d₁| *
            ∑ σ : Equiv.Perm (Fin (d₁ - 1)), θo d₁ (I₁ ∘ σ) i₀) *
            (c ^ (d₁ - 1) * (D.eps i)⁻¹ ^ (d₁ - 1 - (d - 1))) ≤ K * W * (c ^ Dm * S) := by
    intro d₁ hd₁
    have hd₁' := Finset.mem_Icc.mp hd₁
    refine (dirBound_term_le D i Dm hK hW hc0 hθo hℓ hℓE hE he hκ hκ' hκκ hS d d₁ hd
      (by omega) (hold d₁ (by omega) hd₁'.2)).trans ?_
    have : c ^ (d₁ - 1) ≤ c ^ Dm := pow_le_pow_right₀ hc (by omega)
    gcongr
  have hB : (D.eps i / ℓ) ^ (d - 2) * dirBound D i (i + 1) Dm Dγ K W c 1 θo d ≤
      (Dm + 1) * (K * W * (c ^ Dm * S)) := by
    unfold dirBound
    rw [← mul_assoc ((D.eps i / ℓ) ^ (d - 2)), Finset.mul_sum]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    have hcard : ((Dγ + 1 - (d - 1 + 1) : ℕ) : ℝ) ≤ Dm + 1 := by
      have : Dγ + 1 - (d - 1 + 1) ≤ Dm + 1 := by omega
      exact_mod_cast this
    have : 0 ≤ K * W * (c ^ Dm * S) := by positivity
    gcongr
  have hcount : ((Fintype.card (DerivativeWord2 (d - 1)) * 2 : ℕ) : ℝ) ≤ 2 ^ Dm := by
    have h1 : Fintype.card (DerivativeWord2 (d - 1)) * 2 = 2 ^ d := by
      simp only [DerivativeWord2, DerivativeWord, Fintype.card_fun, Fintype.card_fin]
      rw [← pow_succ]
      congr 1
      omega
    rw [h1]
    exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (hdD.trans hDγ)
  have hdB0 : 0 ≤ dirBound D i (i + 1) Dm Dγ K W c 1 θo d :=
    dirBound_nonneg D i (i + 1) Dm Dγ 1 hK hW hc0 hE.le hθo d
  calc (D.eps i / ℓ) ^ (d - 2) * ∑ _α : DerivativeWord2 (d - 1), ∑ _c' : Fin 2,
        Wr * dirBound D i (i + 1) Dm Dγ K W c 1 θo d
      = ((Fintype.card (DerivativeWord2 (d - 1)) * 2 : ℕ) : ℝ) * Wr *
          ((D.eps i / ℓ) ^ (d - 2) * dirBound D i (i + 1) Dm Dγ K W c 1 θo d) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2 ^ Dm * Wr * ((Dm + 1) * (K * W * (c ^ Dm * S))) := by
        have : 0 ≤ (D.eps i / ℓ) ^ (d - 2) * dirBound D i (i + 1) Dm Dγ K W c 1 θo d := by
          positivity
        gcongr
    _ = (2 ^ Dm * (Dm + 1) * Wr * K * W * c ^ Dm) * S := by ring
end

/-! **Ledger: the ledger of a transferred direct copy.** For a new identity `γ'` of `G'` whose
source is the direct copy of the old identity `γ₀` of `G` (`copyDir`), the witnesses
`θ(d, α, c) = W_r · dirBound(d)` satisfy the conclusion of `successor_ledger`
(`copyDir_ledger_case`):
* the expressions are the explicit transfers of the wrapped certified old coefficients
  (`transferExprAt … cfinCopyDir`): generated (`isExprFor_transferExprAt`, `hcfin_copyDir`), with
  certified leaves (`leavesCertified_oldLeaf`) and no uncertified solved node;
* the ledger sum is at most `W_r` times the time- and slot-uniform structural bound `dirBound`
  (`ledgerSum_le`, `genNorm_copyDir_le_dirBound`);
* the record bound holds with the new record size `C_w · S_old` as soon as
  `C_w ≥ 2^{D_m}(D_m+1) W_r K W c^{D_m}` (`dirBound_record_le`), given the old length
  `ℓ ≤ ε_{m-1}` and `κ_m ≤ κ_{m-1}`. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts}

theorem solvedFree_transferExprAt
    (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)) (i : ℕ)
    (lam : ℝ) (Dγ d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (cfin : (p : OddSlot) → (k : ℤ) → (d₁ : ℕ) → DerivativeWord2 (d₁ - 1) → Fin 2 →
      Gen .fam (i + 1) k)
    (hc : ∀ p k d₁ I₁ i₀, Gen.SolvedFree leaf (cfin p k d₁ I₁ i₀)) (p : OddSlot) :
    Gen.SolvedFree leaf (transferExprAt D i lam Dγ d I c cfin p) := by
  unfold transferExprAt
  split_ifs
  · exact solvedFree_transferExpr leaf i p.1 _ _ Dγ d I c (cfin p) (hc p)
  · trivial

open scoped Classical in
/-- **The ledger of a transferred direct copy.** -/
theorem copyDir_ledger_case (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G G' : GenStage D hr Dm b j₀) (hcert : G.OldCert G.exports (compReserve kI) kI.Lstar 1)
    (hexpU : ∀ {i p} (e : Gen .ctx i p), G.exports e → ∀ f f', Gen.Denotes D b j₀ e f →
      Gen.Denotes D b j₀ e f' → AgreeOn D b j₀ i p .ctx f f')
    (hexp : ∀ {i p} (e : Gen .ctx i p), G.exports e → G'.exports e)
    (hlev : G.level = G'.level + 1) {v₀ u₀ : CompIn G.comps} (γ₀ : G.fam.Γ v₀ u₀) (ρ s₀ : ℝ)
    (t₀ : List WordLetter)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin ((SuccSource.copyDir t₀ v₀ u₀ γ₀).pathLen + 1))
      (fun _ => ℝ))
    {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u') (Dγ : ℕ)
    (hflux : ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G'.level p) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
      G'.fam.flux p ctx v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (ctx.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D G.level p.1 1 Dγ ((SuccSource.copyDir t₀ v₀ u₀ γ₀).fluxOp ρ s₀ Cc) t
          (ctx.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    (hDγ : Dγ = (G.fam.identity v₀ u₀ γ₀).maxOrder)
    (hmax' : (G'.fam.identity v' u' γ').maxOrder = Dγ)
    (hlen' : (G'.fam.identity v' u' γ').record.length = (G.fam.identity v₀ u₀ γ₀).record.length)
    {Cw : ℝ}
    (hsize' : (G'.fam.identity v' u' γ').record.size = Cw * (G.fam.identity v₀ u₀ γ₀).record.size)
    (hℓE : (G.fam.identity v₀ u₀ γ₀).record.length ≤ D.eps G'.level)
    (hres : compReserve kI v'.1 ≤ compReserve kI v₀.1)
    (hε : ∀ k, 0 ≤ D.eps k) (hε0 : 0 < D.eps G'.level) (hε1 : D.eps G'.level ≤ 1)
    (he : 0 < D.eps G.level) (hτ : 0 < ocTau D.α D.q D.Λ (G'.level + 1))
    (hκ : 0 < D.kap G'.level) (hκ' : 0 ≤ D.kap G.level) (hκκ : D.kap G.level ≤ D.kap G'.level)
    (κc : MajConsts) {a Δ K W Cold Wr : ℝ} (ha3 : 3 * Real.pi * b < a) (hΔ : 0 < Δ)
    (hresΔ : compReserve kI v'.1 + Dm * Δ ≤ 2) (hK0 : 0 ≤ K) (hW0 : 0 ≤ W) (hC0 : 0 ≤ Cold)
    (hWr0 : 0 ≤ Wr) (hK : ∀ L, L ≤ Dm → kBound κc a L ≤ ENNReal.ofReal K)
    (hW : wsum a 0 κc.child ≤ ENNReal.ofReal W) (hCold : κc.Cold ≤ ENNReal.ofReal Cold)
    (hWr : wsum (3 * Real.pi * b) kI.Lstar (expProfile 1 a) ≤ ENNReal.ofReal Wr)
    (hCw : 2 ^ Dm * (Dm + 1) * Wr * K * W * tConst K Cold Δ ^ Dm ≤ Cw) :
    ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
      (∀ d α c, 0 ≤ θ d α c) ∧
      (∀ d, 2 ≤ d → d ≤ (G'.fam.identity v' u' γ').maxOrder →
        (D.eps G'.level / (G'.fam.identity v' u' γ').record.length) ^ (d - 2) *
            ∑ α, ∑ c, θ d α c ≤ (G'.fam.identity v' u' γ').record.size) ∧
      ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
        ∃ (e : (p : OddSlot) → Gen .ctx G'.level p.1) (Δ : ℝ)
          (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
          G'.IsExprFor v' u' γ' d α c e ∧ 0 < Δ ∧ LeavesCertified D b j₀ leaf ∧
          (∀ p, Gen.SolvedFree leaf (e p)) ∧
          ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) *
              (1 + |(h : ℝ)|) ^ kI.Lstar) *
            ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1,
              genMode D κc Δ leaf (e p) (compReserve kI v'.1) h t
            ≤ ENNReal.ofReal (θ d α c) := by
  have hDm : Dγ ≤ Dm := hDγ ▸ (G.fam.identity v₀ u₀ γ₀).le_D
  have hθo := (oldTheta_spec hcert v₀ u₀ γ₀).1
  have hc1 := one_le_tConst hK0 hC0 hΔ
  have ha0 : 0 ≤ a := by have := mul_pos Real.pi_pos hb; linarith
  refine ⟨fun d _ _ => Wr * dirBound D G'.level G.level Dm Dγ K W (tConst K Cold Δ) 1
    (oldTheta hcert v₀ u₀ γ₀) d, fun d α c => mul_nonneg hWr0
    (dirBound_nonneg D _ _ Dm Dγ 1 hK0 hW0 (by linarith) hε0.le hθo d), fun d hd hdD => ?_,
    fun d α c => ?_⟩
  · -- the record bound
    rw [hlen', hsize']
    rw [hmax'] at hdD
    have hold : ∀ d₁, 2 ≤ d₁ → d₁ ≤ Dγ → (D.eps (G'.level + 1) /
        (G.fam.identity v₀ u₀ γ₀).record.length) ^ (d₁ - 2) *
        ∑ J : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2, oldTheta hcert v₀ u₀ γ₀ d₁ J i₀ ≤
        (G.fam.identity v₀ u₀ γ₀).record.size := fun d₁ h1 h2 => by
      rw [← hlev]
      exact ((oldTheta_spec hcert v₀ u₀ γ₀).2 d₁ h1 (hDγ ▸ h2)).trans_eq (one_mul _)
    have hS0 := (G.fam.identity v₀ u₀ γ₀).record.size_nonneg
    have hb' : D.kap (G'.level + 1) ≤ D.kap G'.level := hlev ▸ hκκ
    have hrec := dirBound_record_le D G'.level Dm Dγ hDm hK0 hW0 hc1 hWr0 hθo
      (G.fam.identity v₀ u₀ γ₀).record.length_pos hℓE hε0 (hlev ▸ he) hκ (hlev ▸ hκ') hb' hS0
      hold d hd hdD
    rw [← hlev] at hrec
    refine hrec.trans ?_
    exact mul_le_mul_of_nonneg_right hCw hS0
  · -- the expressions
    have hlev' : G.level = G'.level + 1 := hlev
    refine ⟨transferExprAt D G'.level 1 Dγ d α c (cfinCopyDir hcert hlev' γ₀), Δ, oldLeaf hcert,
      ?_, hΔ, leavesCertified_oldLeaf hΛ hζ hb hstart hexpU hcert,
      solvedFree_transferExprAt (oldLeaf hcert) G'.level 1 Dγ d α c _
        (fun p k d₁ I₁ i₀ => solvedFree_cfinCopyDir hcert hlev' γ₀ p k d₁ I₁ i₀), ?_⟩
    · refine isExprFor_transferExprAt hζ hΛ hb hstart G' (𝒮 := G.exports) hexp γ' d α c 1 Dγ
        ((SuccSource.copyDir t₀ v₀ u₀ γ₀).fluxOp ρ s₀ Cc) (fun hd p ctx t X z => ?_)
        (cfinCopyDir hcert hlev' γ₀) fun p k hk _ d₁ hd₁ I₁ i₀ => ?_
      · rw [hflux p ctx d α t X z hd, hlev']
      · have hd₁' : 1 ≤ d₁ := by
          have := (Finset.mem_Icc.mp hd₁).1
          omega
        exact hcfin_copyDir hζ hΛ hb hcert hlev' γ₀ ρ s₀ t₀ Cc p k hk d₁ hd₁' I₁ i₀
    · -- the ledger sum
      refine (ledgerSum_le D κc Δ (3 * Real.pi * b) (oldLeaf hcert) (by positivity) _ ha0
        (3 * Real.pi * b) kI.Lstar (compReserve kI v'.1)
        (ENNReal.ofReal (dirBound D G'.level G.level Dm Dγ K W (tConst K Cold Δ) 1
          (oldTheta hcert v₀ u₀ γ₀) d)) fun p t _ => ?_).trans ?_
      · exact genNorm_copyDir_le_dirBound κc Δ _ hcert hb.le hε hlev' hτ hε0 hε1 hΔ γ₀ 1 Dγ d
          hDm α c p a _ t hres (by linarith) le_rfl hK0 hW0 hC0 hK hW hCold
      · show _ ≤ ENNReal.ofReal (Wr * dirBound D G'.level G.level Dm Dγ K W (tConst K Cold Δ) 1
          (oldTheta hcert v₀ u₀ γ₀) d)
        rw [ENNReal.ofReal_mul hWr0]
        exact mul_le_mul_left hWr _
end

end AVRegularity.Providers.CascadeInvariants
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the path weight of a path of the old stage.** The edge sizes `pathTheta` of a path
of `h` edges are supported on the steps `u → u + 1`, so the path weight of grade `h` from the
first to the last vertex is the product of the step sizes (`pathW_pathTheta`): each edge of the
path contributes exactly once. A step size is at most `D_m` times the record size of its identity
(`edgeTheta_le`): the certified ledger entries of the order `d` sum to at most
`(ℓ/ε_m)^{d-2} · size ≤ size`, because a higher identity has length `ℓ ≤ ε_m` (the cell size of a
constituent is at most its tagged size). -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

theorem pathW_succ_eq {ι : Type} [Fintype ι] [DecidableEq ι] (Θ : ι → ι → ℝ≥0) (k : ℕ)
    (v w : ι) : pathW Θ (k + 1) v w = ∑ u, Θ v u * pathW Θ k u w := by
  simp only [pathW]
  rw [pow_succ', Matrix.mul_apply]
  rfl

/-- **The path weight of sizes supported on the steps `u → u + 1`** is the product of the step
sizes. -/
theorem pathW_subdiag {h : ℕ} (Θ : Fin (h + 1) → Fin (h + 1) → ℝ≥0) (g : ℕ → ℝ≥0)
    (hΘ : ∀ v u : Fin (h + 1), Θ v u = if (v : ℕ) = (u : ℕ) + 1 then g u else 0) :
    ∀ k, k ≤ h → ∀ v : Fin (h + 1),
      pathW Θ k v 0 = if (v : ℕ) = k then ∏ j ∈ Finset.range k, g j else 0 := by
  intro k
  induction k with
  | zero =>
    intro _ v
    rw [pathW_zero]
    by_cases hv : v = 0
    · subst hv
      simp
    · have : (v : ℕ) ≠ 0 := fun h0 => hv (Fin.ext h0)
      simp [hv, this]
  | succ k ih =>
    intro hk v
    rw [pathW_succ_eq]
    have hterm : ∀ u : Fin (h + 1), u ≠ ⟨k, by omega⟩ → Θ v u * pathW Θ k u 0 = 0 := by
      intro u hu
      have hne : (u : ℕ) ≠ k := fun h0 => hu (Fin.ext h0)
      rw [ih (by omega) u]
      simp [hne]
    rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin (h + 1)) (fun u _ hu => hterm u hu)
      (fun hn => absurd (Finset.mem_univ _) hn), ih (by omega), hΘ]
    simp only [↓reduceIte]
    by_cases hv : (v : ℕ) = k + 1
    · simp only [hv, ↓reduceIte]
      rw [Finset.prod_range_succ, mul_comm]
    · simp [hv]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {𝒮o : SeedExports} {μo : Comp → ℝ} {Lo : ℕ} {Co : ℝ}
  {G : GenStage D hr Dm b j₀}

/-- **The path weight of a path of the old stage** is the product of the sizes of its steps. -/
theorem pathW_pathTheta (hcert : G.OldCert 𝒮o μo Lo Co) {h : ℕ} (π : StagePath G h) :
    pathW (pathTheta hcert π) h (Fin.last h) 0 =
      ∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2 := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ≥0, ∀ (j : ℕ) (hj : j < h), g j =
      edgeTheta hcert (π.step ⟨j, hj⟩).1 (π.step ⟨j, hj⟩).2.1 (π.step ⟨j, hj⟩).2.2 :=
    ⟨fun j => if hj : j < h then
      edgeTheta hcert (π.step ⟨j, hj⟩).1 (π.step ⟨j, hj⟩).2.1 (π.step ⟨j, hj⟩).2.2 else 1,
      fun j hj => by simp only [hj, ↓reduceDIte]⟩
  have hΘ : ∀ v u : Fin (h + 1), pathTheta hcert π v u =
      if (v : ℕ) = (u : ℕ) + 1 then g u else 0 := by
    intro v u
    unfold pathTheta
    by_cases hvu : (v : ℕ) = (u : ℕ) + 1
    · have hu : (u : ℕ) < h := by have := v.2; omega
      simp only [hvu, hu, and_self, ↓reduceDIte, ↓reduceIte]
      exact (hg u hu).symm
    · simp only [hvu, false_and, ↓reduceDIte, ↓reduceIte]
  rw [pathW_subdiag _ g hΘ h le_rfl (Fin.last h)]
  simp only [Fin.val_last, ↓reduceIte]
  rw [Finset.prod_range]
  exact Finset.prod_congr rfl fun j _ => hg j j.2

/-- **A step size is at most `D_m` times the record size of its identity** (times the record
factor `Co` of the certificate). -/
theorem edgeTheta_le (hcert : G.OldCert 𝒮o μo Lo Co) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hℓ : 3 ≤ (G.fam.identity v u γ).maxOrder →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level) :
    edgeTheta hcert v u γ ≤
      (Dm : ℝ≥0) * Real.toNNReal (Co * (G.fam.identity v u γ).record.size) := by
  have hθ := oldTheta_spec hcert v u γ
  have hlen := (G.fam.identity v u γ).record.length_pos
  have hd : ∀ d ∈ Finset.Icc 2 (G.fam.identity v u γ).maxOrder,
      ∑ α : DerivativeWord2 (d - 1), ∑ c : Fin 2, Real.toNNReal (oldTheta hcert v u γ d α c) ≤
        Real.toNNReal (Co * (G.fam.identity v u γ).record.size) := by
    intro d hd
    have hd' := Finset.mem_Icc.mp hd
    have hsum0 : 0 ≤ ∑ α : DerivativeWord2 (d - 1), ∑ c : Fin 2, oldTheta hcert v u γ d α c :=
      Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun c _ => hθ.1 d α c
    have hone : 1 ≤ (D.eps G.level / (G.fam.identity v u γ).record.length) ^ (d - 2) := by
      rcases Nat.lt_or_ge d 3 with h3 | h3
      · obtain rfl : d = 2 := by omega
        simp
      · exact one_le_pow₀ ((one_le_div hlen).mpr (hℓ (h3.trans hd'.2)))
    have hle : ∑ α : DerivativeWord2 (d - 1), ∑ c : Fin 2, oldTheta hcert v u γ d α c ≤
        Co * (G.fam.identity v u γ).record.size :=
      (le_mul_of_one_le_left hsum0 hone).trans (hθ.2 d hd'.1 hd'.2)
    have hcast : ∑ α : DerivativeWord2 (d - 1), ∑ c : Fin 2,
        Real.toNNReal (oldTheta hcert v u γ d α c) =
        Real.toNNReal (∑ α : DerivativeWord2 (d - 1), ∑ c : Fin 2, oldTheta hcert v u γ d α c) := by
      rw [Real.toNNReal_sum_of_nonneg fun α _ => Finset.sum_nonneg fun c _ => hθ.1 d α c]
      exact Finset.sum_congr rfl fun α _ =>
        (Real.toNNReal_sum_of_nonneg fun c _ => hθ.1 d α c).symm
    rw [hcast]
    exact Real.toNNReal_le_toNNReal hle
  unfold edgeTheta
  refine (Finset.sum_le_sum hd).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Icc 2 (G.fam.identity v u γ).maxOrder).card : ℝ≥0) ≤ Dm := by
    have h1 := (G.fam.identity v u γ).le_D
    rw [Nat.card_Icc]
    exact_mod_cast (by omega : (G.fam.identity v u γ).maxOrder + 1 - 2 ≤ Dm)
  gcongr
end

/-! **Ledger: the transferred coefficient from graded finer outputs.** If the finer outputs of a
source over every odd finer slot are graded slot family functions (`SlotFamRepP`) with reserve
costs `r d₁` and sizes `C d₁`, then the explicit transfer of chosen finer expressions
* is generated (`IsExprFor`, by `isExprFor_transferExprAt`),
* has no uncertified solved node,
* and at every slot and time has structural norm at most
  `|C_d| Σ_{d₁, I₁, i₀} K · W_child · C d₁ · T_{d₁-1, d-1}` (and `0` below the tested order two),
  uniformly: the finer slots enter as a sub-convex combination of the cutoff weights
  (`genNorm_transferExpr_le`). The reserve is needed for the orders `d ≥ 2` only.
This is the source-independent step of the ledger of every source with a transfer. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- **The transferred coefficient from graded finer outputs.** -/
theorem exists_transferExpr_of_finer (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G' : GenStage D hr Dm b j₀) {𝒮 : SeedExports}
    (hexp : ∀ {i p} (e : Gen .ctx i p), 𝒮 e → G'.exports e)
    {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u') (d : ℕ) (I : DerivativeWord2 (d - 1))
    (c : Fin 2) (lam : ℝ) (Dγ : ℕ) (fop : FamFluxOp)
    (hflux : 2 ≤ d → ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G'.level p) (t : ℝ) (Y z : Vec 2),
      G'.fam.flux p ctx v' u' γ' d I t Y z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (ctx.1.recenter D (D.eps (G'.level - 1) • Y))
        then transferAt D (G'.level + 1) p.1 lam Dγ fop t
          (ctx.1.recenter D (D.eps (G'.level - 1) • Y)) z d I
        else 0)
    {X : GCtx} (hXT : ∀ t, t ∈ X.T)
    (hlev : ∀ (s : GenSort) (p : ℤ) (e : Gen s G'.level p), X.leaf e = none)
    (hτ : 0 < ocTau D.α D.q D.Λ (G'.level + 1)) {r : ℕ → ℕ} {C : ℕ → ℝ≥0}
    (hfine : ∀ k : ℤ, Odd k → ∀ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ,
      ∀ (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
        SlotFamRepP D b j₀ 𝒮 (G'.level + 1) k X
          (fun t A => fluxCoeff (fop k t A) d₁ I₁ 0 i₀) (r d₁) (C d₁))
    {mres : ℝ} (hmres : 2 ≤ d → ∀ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ, mres + r d₁ * X.Δ ≤ X.μ₀) :
    ∃ e : (p : OddSlot) → Gen .ctx G'.level p.1,
      G'.IsExprFor v' u' γ' d I c e ∧ (∀ p, Gen.SolvedFree X.leaf (e p)) ∧
      ∀ (p : OddSlot) (a : ℝ) (L : ℕ) (t : ℝ),
        genNorm D X.κ X.Δ X.a₀ X.leaf (e p) a mres L t ≤
          if 2 ≤ d then
            ENNReal.ofReal |(D.kap G'.level * D.eps G'.level ^ (d - 2))⁻¹ * lam| *
              ∑ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ, ∑ _I₁ : DerivativeWord2 (d₁ - 1), ∑ _i₀ : Fin 2,
                kBound X.κ a L * wsum a L X.κ.child * (C d₁ : ℝ≥0∞) *
                  tBound D X.κ X.Δ a G'.level (d₁ - 1) (d - 1) mres L
          else 0 := by
  have hch : ∀ (k : ℤ) (d₁ : ℕ) (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
      ∃ cf : Gen .fam (G'.level + 1) k,
        (Odd k → d₁ ∈ Finset.Icc (d - 1 + 1) Dγ →
          Gen.IsScheduled D cf ∧ Gen.FromSeed 𝒮 cf ∧
          (∃ fc : GenSort.Sem .fam, Gen.Denotes D b j₀ cf fc ∧
            ∀ A, IsAdmissibleChain D b j₀ (G'.level + 1) k A →
              ∀ t ∈ ocPulseWindow D.α D.q D.Λ (G'.level + 1) k,
                fc t A = fluxCoeff (fop k t A) d₁ I₁ 0 i₀) ∧
          Gen.SolvedFree X.leaf cf ∧
          ∀ t ∈ X.T, ∀ mres', mres' + r d₁ * X.Δ ≤ X.μ₀ →
            genNorm D X.κ X.Δ X.a₀ X.leaf cf X.a₀ mres' 0 t ≤ C d₁) ∧
        (¬(Odd k ∧ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ) → cf = Gen.time (.const 0)) := by
    intro k d₁ I₁ i₀
    by_cases h : Odd k ∧ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ
    · obtain ⟨cf, h1, h2, h3, h4, h5⟩ := hfine k h.1 d₁ h.2 I₁ i₀
      exact ⟨cf, fun _ _ => ⟨h1, h2, h3, h4, h5⟩, fun hn => absurd h hn⟩
    · exact ⟨Gen.time (.const 0), fun h1 h2 => absurd ⟨h1, h2⟩ h, fun _ => rfl⟩
  choose cf hcf hcf0 using hch
  refine ⟨transferExprAt D G'.level lam Dγ d I c (fun _ k d₁ I₁ i₀ => cf k d₁ I₁ i₀), ?_, ?_, ?_⟩
  · refine isExprFor_transferExprAt hζ hΛ hb hstart G' hexp γ' d I c lam Dγ fop hflux _
      fun p k hk _ d₁ hd₁ I₁ i₀ => ?_
    obtain ⟨h1, h2, h3, -, -⟩ := hcf k d₁ I₁ i₀ hk hd₁
    exact ⟨h1, h2, h3⟩
  · refine solvedFree_transferExprAt X.leaf G'.level lam Dγ d I c _ fun p k d₁ I₁ i₀ => ?_
    by_cases h : Odd k ∧ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ
    · exact (hcf k d₁ I₁ i₀ h.1 h.2).2.2.2.1
    · rw [hcf0 k d₁ I₁ i₀ h]
      trivial
  · intro p a L t
    unfold transferExprAt
    split_ifs with hd
    · refine genNorm_transferExpr_le D X.κ X.Δ X.a₀ X.leaf hlev hτ _ _
        (finerSlots_odd D G'.level p.1) Dγ d I c _ a mres L t _ fun k hk => ?_
      refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun I₁ _ =>
        Finset.sum_le_sum fun i₀ _ => ?_
      exact mul_le_mul_left (mul_le_mul_right
        ((hcf k d₁ I₁ i₀ (finerSlots_odd D G'.level p.1 k hk) hd₁).2.2.2.2 t (hXT t) mres
          (hmres hd d₁ hd₁)) _) _
    · exact (genNorm_const_le (D := D) X.κ X.Δ X.a₀ X.leaf 0 (hlev _ _ _) a mres L t).trans
        (by simp)
end

/-! **Ledger: the ledger arithmetic of the path means.** For a source whose finer outputs are the
path means of cell degree `n` of a path (`copyQuad`: `n = 2`; `letterMean`: `n ≥ 3`):
* the scale identity `pm_scale_identity`: with `d_*² = κ ℓ²`,
  `(κ E^k)⁻¹ · ℓ⁻²(d_*/ρ)^{2+j} ρ · ρ^{k+i+1} · E^{-i} = (d_*/ρ)^j (ρ/E)^{k+i}`: all powers of `ρ`
  and `E` cancel exactly, leaving the gain `(d_*/ρ)^{n-2}` and the lowering factor `(ρ/E)^{d₁-2}`;
  
* the real majorant `pmBound` of the transferred coefficient and its bound of the structural norm
  (`pm_genNorm_le`);
* its tagged size (`pmBound_record_le`): at most
  `4^{D_m}(D_m+1)c^{D_m} · W_r K W Q · |λ| (d_*/ρ)^{n-2} · FP`, where `Q` bounds
  `(E/ℓ')^{d-2}(ρ/E)^{d-2+j}` (the new length against the lift length). -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-- **The scale identity of the path-mean price.** -/
theorem pm_scale_identity {B E ρ Lsq Dst : ℝ} (hB : B ≠ 0) (hρ : ρ ≠ 0) (hL : Lsq ≠ 0)
    (hD : Dst ^ 2 = B * Lsq) (k i j : ℕ) :
    (B * E ^ k)⁻¹ * (Lsq⁻¹ * (Dst / ρ) ^ (2 + j) * ρ * ρ ^ (k + i + 1)) * E⁻¹ ^ i =
      (Dst / ρ) ^ j * (ρ / E) ^ (k + i) := by
  have h1 : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
  have h2 : B * B⁻¹ = 1 := mul_inv_cancel₀ hB
  have h3 : Lsq * Lsq⁻¹ = 1 := mul_inv_cancel₀ hL
  linear_combination
    (Dst ^ j * ρ⁻¹ ^ j * ρ ^ (k + i) * E⁻¹ ^ (k + i)) * (B⁻¹ * Lsq⁻¹ * ρ⁻¹ ^ 2 * ρ ^ 2) * hD +
    (Dst ^ j * ρ⁻¹ ^ j * ρ ^ (k + i) * E⁻¹ ^ (k + i)) * (Lsq * Lsq⁻¹) * (ρ * ρ⁻¹) ^ 2 * h2 +
    (Dst ^ j * ρ⁻¹ ^ j * ρ ^ (k + i) * E⁻¹ ^ (k + i)) * (ρ * ρ⁻¹) ^ 2 * h3 +
    (Dst ^ j * ρ⁻¹ ^ j * ρ ^ (k + i) * E⁻¹ ^ (k + i)) * (ρ * ρ⁻¹ + 1) * h1

/-- **The real majorant of a transferred path mean** of cell degree `n`, at the tested order `d`
of the coarse level `i`, from the old level `m`, with the lift length `ρ`; `FP` is the lift
constant times the product of the edge sizes. -/
def pmBound (D : OCData) (i m : ℕ) (ρ : ℝ) (n Dγ : ℕ) (K W c lam FP : ℝ) (d : ℕ) : ℝ :=
  |(D.kap i * D.eps i ^ (d - 2))⁻¹ * lam| *
    ∑ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ, ∑ _I₁ : DerivativeWord2 (d₁ - 1), ∑ _i₀ : Fin 2,
      K * W * (|LiftGenSetup.pathMeanPref D m ρ n d₁| * (((d₁ - 1).factorial : ℝ) * FP)) *
        (c ^ (d₁ - 1) * (D.eps i)⁻¹ ^ (d₁ - 1 - (d - 1)))

theorem pmBound_nonneg (D : OCData) (i m : ℕ) (ρ : ℝ) (n Dγ : ℕ) {K W c : ℝ} (lam : ℝ) {FP : ℝ}
    (hK : 0 ≤ K) (hW : 0 ≤ W) (hc : 0 ≤ c) (hε : 0 ≤ D.eps i) (hF : 0 ≤ FP) (d : ℕ) :
    0 ≤ pmBound D i m ρ n Dγ K W c lam FP d := by
  unfold pmBound
  refine mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun d₁ _ => Finset.sum_nonneg fun I₁ _ =>
    Finset.sum_nonneg fun i₀ _ => ?_)
  positivity

/-- **The transferred path mean is bounded by its real majorant.** -/
theorem pm_genNorm_le (D : OCData) (κc : MajConsts) {Δ a : ℝ} {i : ℕ} (hε0 : 0 < D.eps i)
    (hε1 : D.eps i ≤ 1) (hΔ : 0 < Δ) (m : ℕ) (ρ : ℝ) (n Dγ Dm : ℕ) (hDγ : Dγ ≤ Dm) (lam : ℝ)
    (FP : ℝ≥0) {K W Cold : ℝ} (hK0 : 0 ≤ K) (hW0 : 0 ≤ W) (hC0 : 0 ≤ Cold)
    (hK : ∀ L, L ≤ Dm → kBound κc a L ≤ ENNReal.ofReal K)
    (hW : wsum a 0 κc.child ≤ ENNReal.ofReal W) (hCold : κc.Cold ≤ ENNReal.ofReal Cold)
    {mres : ℝ} (hres : mres + Dm * Δ ≤ 2) (d : ℕ) :
    ENNReal.ofReal |(D.kap i * D.eps i ^ (d - 2))⁻¹ * lam| *
        ∑ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ, ∑ _I₁ : DerivativeWord2 (d₁ - 1), ∑ _i₀ : Fin 2,
          kBound κc a 0 * wsum a 0 κc.child *
            ((Real.toNNReal |LiftGenSetup.pathMeanPref D m ρ n d₁| *
              (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) * FP) : ℝ≥0) :
              ℝ≥0∞) * tBound D κc Δ a i (d₁ - 1) (d - 1) mres 0 ≤
      ENNReal.ofReal (pmBound D i m ρ n Dγ K W (tConst K Cold Δ) lam FP d) := by
  have hc0 := tConst_nonneg hK0 hC0 hΔ
  have hF0 : (0 : ℝ) ≤ FP := FP.2
  unfold pmBound
  refine mul_le_ofReal_mul (abs_nonneg _) le_rfl ?_
  refine sum_le_ofReal_sum (fun d₁ _ => Finset.sum_nonneg fun I₁ _ => Finset.sum_nonneg
    fun i₀ _ => ?_) fun d₁ hd₁ => sum_le_ofReal_sum (fun I₁ _ => Finset.sum_nonneg
    fun i₀ _ => ?_) fun I₁ _ => sum_le_ofReal_sum (fun i₀ _ => ?_) fun i₀ _ => ?_
  · positivity
  · positivity
  · positivity
  · have hd₁' := Finset.mem_Icc.mp hd₁
    have hT := (tBound_le D κc hε0 hε1 hΔ hC0 hK0 hCold hK (d₁ - 1) (d - 1) mres 0
      (by
        have : ((d₁ - 1 : ℕ) : ℝ) * Δ ≤ Dm * Δ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : d₁ - 1 ≤ Dm)) hΔ.le
        linarith)
      (by omega)).2 (by omega)
    have hC : ((Real.toNNReal |LiftGenSetup.pathMeanPref D m ρ n d₁| *
        (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) * FP) : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (|LiftGenSetup.pathMeanPref D m ρ n d₁| *
          (((d₁ - 1).factorial : ℝ) * FP)) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      push_cast
      rw [Real.coe_toNNReal _ (abs_nonneg _)]
    rw [hC]
    refine mul_le_ofReal_mul (by positivity) ?_ hT
    refine mul_le_ofReal_mul (by positivity) ?_ le_rfl
    exact mul_le_ofReal_mul hK0 (hK 0 (Nat.zero_le _)) hW

/-- **One order of the transferred path mean against the new length.** With `d = 2 + k`,
`d₁ = 2 + k + i'` and `n = 2 + j`. -/
theorem pmTerm_le (D : OCData) (i m : ℕ) (ρ : ℝ) {K W c lam FP ℓ' Q : ℝ} (hK : 0 ≤ K)
    (hW : 0 ≤ W) (hc : 0 ≤ c) (hF : 0 ≤ FP) (hρ : 0 < ρ) (hκ : 0 < D.kap i)
    (hL : 0 < D.cellScaleSq m)
    (hD : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ 2 = D.kap i * D.cellScaleSq m)
    (hDst : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) (k i' j : ℕ)
    (hQ : (D.eps i / ℓ') ^ k * (ρ / D.eps i) ^ (k + i') ≤ Q) (hE : 0 < D.eps i) :
    (D.eps i / ℓ') ^ k * |(D.kap i * D.eps i ^ k)⁻¹ * lam| *
        (K * W * (|LiftGenSetup.pathMeanPref D m ρ (2 + j) (2 + k + i')| *
          (((k + i' + 1).factorial : ℝ) * FP)) * (c ^ (k + i' + 1) * (D.eps i)⁻¹ ^ i')) ≤
      K * W * c ^ (k + i' + 1) * (Q * |lam| *
        (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ j * FP) := by
  set Dst := ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) with hDstdef
  have hfac : (0 : ℝ) < (k + i' + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hpref : |LiftGenSetup.pathMeanPref D m ρ (2 + j) (2 + k + i')| *
      ((k + i' + 1).factorial : ℝ) =
      (D.cellScaleSq m)⁻¹ * (Dst / ρ) ^ (2 + j) * ρ * ρ ^ (k + i' + 1) := by
    unfold LiftGenSetup.pathMeanPref
    rw [show 2 + k + i' - 1 = k + i' + 1 by omega]
    have hpos : 0 ≤ (D.cellScaleSq m)⁻¹ * (Dst / ρ) ^ (2 + j) * ρ * ρ ^ (k + i' + 1) *
        ((k + i' + 1).factorial : ℝ)⁻¹ := by positivity
    rw [show -((D.cellScaleSq m)⁻¹ * (Dst / ρ) ^ (2 + j) * ρ) * ρ ^ (k + i' + 1) *
        ((k + i' + 1).factorial : ℝ)⁻¹ = -((D.cellScaleSq m)⁻¹ * (Dst / ρ) ^ (2 + j) * ρ *
          ρ ^ (k + i' + 1) * ((k + i' + 1).factorial : ℝ)⁻¹) by ring, abs_neg, abs_of_nonneg hpos,
      inv_mul_cancel_right₀ hfac.ne']
  have hid := pm_scale_identity (E := D.eps i) hκ.ne' hρ.ne' hL.ne' hD k i' j
  have hκE : 0 < D.kap i * D.eps i ^ k := by positivity
  have habs : |(D.kap i * D.eps i ^ k)⁻¹ * lam| = (D.kap i * D.eps i ^ k)⁻¹ * |lam| := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hκE)]
  have hDρ : 0 ≤ (Dst / ρ) ^ j := by positivity
  have hcoef : 0 ≤ K * W * c ^ (k + i' + 1) * (|lam| * FP * (Dst / ρ) ^ j) := by positivity
  calc (D.eps i / ℓ') ^ k * |(D.kap i * D.eps i ^ k)⁻¹ * lam| *
        (K * W * (|LiftGenSetup.pathMeanPref D m ρ (2 + j) (2 + k + i')| *
          (((k + i' + 1).factorial : ℝ) * FP)) * (c ^ (k + i' + 1) * (D.eps i)⁻¹ ^ i'))
      = K * W * c ^ (k + i' + 1) * (|lam| * FP *
          ((D.eps i / ℓ') ^ k * ((D.kap i * D.eps i ^ k)⁻¹ *
            ((D.cellScaleSq m)⁻¹ * (Dst / ρ) ^ (2 + j) * ρ * ρ ^ (k + i' + 1)) *
              (D.eps i)⁻¹ ^ i'))) := by
        rw [habs, ← hpref]
        ring
    _ = K * W * c ^ (k + i' + 1) * (|lam| * FP * (Dst / ρ) ^ j) *
          ((D.eps i / ℓ') ^ k * (ρ / D.eps i) ^ (k + i')) := by
        rw [hid]
        ring
    _ ≤ K * W * c ^ (k + i' + 1) * (|lam| * FP * (Dst / ρ) ^ j) * Q :=
        mul_le_mul_of_nonneg_left hQ hcoef
    _ = _ := by ring

/-- **The tagged size of a transferred path mean.** -/
theorem pmBound_record_le (D : OCData) (i m : ℕ) (ρ : ℝ) {n Dγ Dm : ℕ} (hDγ : Dγ ≤ Dm)
    {K W c Wr lam FP ℓ' Q : ℝ} (hK : 0 ≤ K) (hW : 0 ≤ W) (hc : 1 ≤ c) (hWr : 0 ≤ Wr)
    (hF : 0 ≤ FP) (hρ : 0 < ρ) (hκ : 0 < D.kap i) (hL : 0 < D.cellScaleSq m)
    (hD : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ 2 = D.kap i * D.cellScaleSq m)
    (hDst : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) (hE : 0 < D.eps i) (hℓ' : 0 < ℓ')
    (hn : 2 ≤ n) (d : ℕ) (hd : 2 ≤ d) (hdD : d ≤ Dm) (hQ0 : 0 ≤ Q)
    (hQ : ∀ i', (D.eps i / ℓ') ^ (d - 2) * (ρ / D.eps i) ^ (d - 2 + i') ≤ Q) :
    (D.eps i / ℓ') ^ (d - 2) * ∑ _α : DerivativeWord2 (d - 1), ∑ _c : Fin 2,
        Wr * pmBound D i m ρ n Dγ K W c lam FP d ≤
      4 ^ Dm * (Dm + 1) * c ^ Dm * (Wr * K * W * Q * |lam| *
        (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ (n - 2) * FP) := by
  set Dst := ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) with hDstdef
  have hc0 : 0 ≤ c := by linarith
  have hG0 : 0 ≤ Q * |lam| * (Dst / ρ) ^ (n - 2) * FP := by positivity
  -- one order
  have hterm : ∀ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ,
      (D.eps i / ℓ') ^ (d - 2) * |(D.kap i * D.eps i ^ (d - 2))⁻¹ * lam| *
        (K * W * (|LiftGenSetup.pathMeanPref D m ρ n d₁| * (((d₁ - 1).factorial : ℝ) * FP)) *
          (c ^ (d₁ - 1) * (D.eps i)⁻¹ ^ (d₁ - 1 - (d - 1)))) ≤
        K * W * c ^ Dm * (Q * |lam| * (Dst / ρ) ^ (n - 2) * FP) := by
    intro d₁ hd₁
    have hd₁' := Finset.mem_Icc.mp hd₁
    obtain ⟨k, rfl⟩ : ∃ k, d = 2 + k := ⟨d - 2, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 + j := ⟨n - 2, by omega⟩
    obtain ⟨i', rfl⟩ : ∃ i', d₁ = 2 + k + i' := ⟨d₁ - (2 + k), by omega⟩
    have e1 : 2 + k + i' - 1 = k + i' + 1 := by omega
    have e2 : k + i' + 1 - (2 + k - 1) = i' := by omega
    have e3 : 2 + k - 2 = k := by omega
    have e4 : 2 + j - 2 = j := by omega
    rw [e1, e2, e3, e4]
    have hq := hQ i'
    rw [e3] at hq
    refine (pmTerm_le D i m ρ hK hW hc0 hF hρ hκ hL hD hDst k i' j hq hE).trans ?_
    have hpow : c ^ (k + i' + 1) ≤ c ^ Dm := pow_le_pow_right₀ hc (by omega)
    have hG0' : 0 ≤ Q * |lam| * (Dst / ρ) ^ j * FP := by rw [e4] at hG0; exact hG0
    gcongr
  have hinner : ∀ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ,
      (D.eps i / ℓ') ^ (d - 2) * |(D.kap i * D.eps i ^ (d - 2))⁻¹ * lam| *
        ∑ _I₁ : DerivativeWord2 (d₁ - 1), ∑ _i₀ : Fin 2,
          K * W * (|LiftGenSetup.pathMeanPref D m ρ n d₁| * (((d₁ - 1).factorial : ℝ) * FP)) *
            (c ^ (d₁ - 1) * (D.eps i)⁻¹ ^ (d₁ - 1 - (d - 1))) ≤
        2 ^ Dm * (K * W * c ^ Dm * (Q * |lam| * (Dst / ρ) ^ (n - 2) * FP)) := by
    intro d₁ hd₁
    have hd₁' := Finset.mem_Icc.mp hd₁
    have hcount : ((Fintype.card (DerivativeWord2 (d₁ - 1)) * 2 : ℕ) : ℝ) ≤ 2 ^ Dm := by
      have h1 : Fintype.card (DerivativeWord2 (d₁ - 1)) * 2 = 2 ^ d₁ := by
        simp only [DerivativeWord2, DerivativeWord, Fintype.card_fun, Fintype.card_fin]
        rw [← pow_succ]
        congr 1
        omega
      rw [h1]
      exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (hd₁'.2.trans hDγ)
    have hR0 : 0 ≤ K * W * c ^ Dm * (Q * |lam| * (Dst / ρ) ^ (n - 2) * FP) := by positivity
    calc (D.eps i / ℓ') ^ (d - 2) * |(D.kap i * D.eps i ^ (d - 2))⁻¹ * lam| *
          ∑ _I₁ : DerivativeWord2 (d₁ - 1), ∑ _i₀ : Fin 2,
            K * W * (|LiftGenSetup.pathMeanPref D m ρ n d₁| * (((d₁ - 1).factorial : ℝ) * FP)) *
              (c ^ (d₁ - 1) * (D.eps i)⁻¹ ^ (d₁ - 1 - (d - 1)))
        = ((Fintype.card (DerivativeWord2 (d₁ - 1)) * 2 : ℕ) : ℝ) *
            ((D.eps i / ℓ') ^ (d - 2) * |(D.kap i * D.eps i ^ (d - 2))⁻¹ * lam| *
              (K * W * (|LiftGenSetup.pathMeanPref D m ρ n d₁| *
                (((d₁ - 1).factorial : ℝ) * FP)) *
                (c ^ (d₁ - 1) * (D.eps i)⁻¹ ^ (d₁ - 1 - (d - 1))))) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 2 ^ Dm * (K * W * c ^ Dm * (Q * |lam| * (Dst / ρ) ^ (n - 2) * FP)) :=
          mul_le_mul hcount (hterm d₁ hd₁) (by
            have := hterm d₁ hd₁
            positivity) (by positivity)
  have hB : (D.eps i / ℓ') ^ (d - 2) * pmBound D i m ρ n Dγ K W c lam FP d ≤
      (Dm + 1) * (2 ^ Dm * (K * W * c ^ Dm * (Q * |lam| * (Dst / ρ) ^ (n - 2) * FP))) := by
    unfold pmBound
    rw [← mul_assoc ((D.eps i / ℓ') ^ (d - 2)), Finset.mul_sum]
    refine (Finset.sum_le_sum hinner).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    have hcard : ((Dγ + 1 - (d - 1 + 1) : ℕ) : ℝ) ≤ Dm + 1 := by
      have : Dγ + 1 - (d - 1 + 1) ≤ Dm + 1 := by omega
      exact_mod_cast this
    have : 0 ≤ 2 ^ Dm * (K * W * c ^ Dm * (Q * |lam| * (Dst / ρ) ^ (n - 2) * FP)) := by
      positivity
    gcongr
  have hcount : ((Fintype.card (DerivativeWord2 (d - 1)) * 2 : ℕ) : ℝ) ≤ 2 ^ Dm := by
    have h1 : Fintype.card (DerivativeWord2 (d - 1)) * 2 = 2 ^ d := by
      simp only [DerivativeWord2, DerivativeWord, Fintype.card_fun, Fintype.card_fin]
      rw [← pow_succ]
      congr 1
      omega
    rw [h1]
    exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ 2) hdD
  have hpm0 : 0 ≤ (D.eps i / ℓ') ^ (d - 2) * pmBound D i m ρ n Dγ K W c lam FP d := by
    have h1 := pmBound_nonneg D i m ρ n Dγ lam hK hW hc0 hE.le hF d
    have h2 : 0 ≤ (D.eps i / ℓ') ^ (d - 2) := pow_nonneg (div_nonneg hE.le hℓ'.le) _
    positivity
  calc (D.eps i / ℓ') ^ (d - 2) * ∑ _α : DerivativeWord2 (d - 1), ∑ _c : Fin 2,
        Wr * pmBound D i m ρ n Dγ K W c lam FP d
      = ((Fintype.card (DerivativeWord2 (d - 1)) * 2 : ℕ) : ℝ) * Wr *
          ((D.eps i / ℓ') ^ (d - 2) * pmBound D i m ρ n Dγ K W c lam FP d) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2 ^ Dm * Wr * ((Dm + 1) * (2 ^ Dm * (K * W * c ^ Dm *
          (Q * |lam| * (Dst / ρ) ^ (n - 2) * FP)))) := by
        gcongr
    _ = _ := by
        rw [show (4 : ℝ) ^ Dm = 2 ^ Dm * 2 ^ Dm by rw [← mul_pow]; norm_num]
        ring
end

/-! **Ledger: the graded finer outputs of the path sources.** Over the graded context `oldCtx` of
the certified old coefficients:
* `slotFamRepP_pathMean_of_path`: the path mean of cell degree `n` of a path of the old stage is a
  graded slot family function, with reserve cost `(n-1) - (d-1)` and size
  `|c_{n,d}| (d-1)! · fluxXc · ∏_j edgeTheta(step j)` (from the cut-off lift setup, the graded source
  edges and the path weight);
* `slotFamRepP_directFlux`: the direct flux of an old identity over a finite set of orders is a
  graded slot family function, with no reserve and size `|c_d| Σ_σ θ_old(d, I∘σ, i₀)`. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {𝒮o : SeedExports} {μo : Comp → ℝ} {Lo : ℕ} {Co : ℝ}
  {G : GenStage D hr Dm b j₀}

/-- **The path mean of a path of the old stage is a graded slot family function.** -/
theorem slotFamRepP_pathMean_of_path (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 ≤ b) (hεn : ∀ k, 0 ≤ D.eps k)
    (hcert : G.OldCert 𝒮o μo Lo Co) (hT : G.IsSlotTransverse) {h : ℕ} (π : StagePath G h)
    (k : ℤ) (hk : Odd k) (ρ : ℝ)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) {sX sZ N R : ℕ}
    (hset : CutoffLiftSetup D b j₀ 𝒮o G.level k ρ (pathEdgesAt G π ⟨k, hk⟩) Cc sX sZ N R)
    (κ : MajConsts) {Δ μ₀ : ℝ} {S Kg Kd : ℝ≥0} (hXok : (oldCtx hcert κ Δ μ₀ S Kg Kd).Ok)
    (hμ : ∀ j : Fin h, μ₀ ≤ μo (π.step j).1.1)
    (hSl : ENNReal.ofReal |ρ| * (κ.Cslow / ENNReal.ofReal (D.eps (G.level - 1) * Δ)) ≤ S)
    (hη0 : 0 ≤ D.kap G.level / D.kap (G.level - 1))
    (hη1 : D.kap G.level / D.kap (G.level - 1) ≤ 1) (hL₀ : UEnv.liftWt Dm h N ≤ Lo)
    {n : ℕ} (hn1 : 1 ≤ n) (hLn : UEnv.liftWt Dm h n ≤ Lo) (hnR : n + Dm + 2 ≤ R) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (κ' : Fin 2) :
    SlotFamRepP D b j₀ 𝒮o G.level k (oldCtx hcert κ Δ μ₀ S Kg Kd) (fun t A =>
      fluxCoeff (pathMeanFlux D G.level ρ
        (familyLiftData D G.level k A ρ (pathEdgesAt G π ⟨k, hk⟩ A)) (Cc A) n t) d I 0 κ')
      (n - 1 - (d - 1))
      (Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ n d| *
        (((Finset.univ : Finset (Equiv.Perm (Fin (d - 1)))).card : ℝ≥0) *
          (UEnv.fluxXc (oldCtx hcert κ Δ μ₀ S Kg Kd) Dm
            (liftB (oldCtx hcert κ Δ μ₀ S Kg Kd) Dm) h n *
            ∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2))) := by
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have h1 := CutoffLiftSetup.slotFamRep_pathMeanP hset hc hXok hSl hη0 hη1
    (Θ := pathTheta hcert π)
    (fun U hU v u d α c => edgeURepP_of_certified hb hεn hcert hT π ⟨k, hk⟩ rfl rfl hε _ U _ _
      (fun A hA => hA) (fun A hA Y hY => hU A hA hY)
      (fun τ hτ => cellScaleSq_mul_mem_ocPulseWindow hc hτ) κ hXok hμ v u d α c)
    hL₀ hn1 hLn hnR d I κ'
  rwa [pathW_pathTheta] at h1

open scoped Classical in
/-- **The direct flux of an old identity is a graded slot family function.** -/
theorem slotFamRepP_directFlux (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b)
    (hεn : ∀ k, 0 ≤ D.eps k) (hcert : G.OldCert G.exports μo Lo Co) {v u : CompIn G.comps}
    (γ : G.fam.Γ v u) (ords : Finset ℕ) (hords : ∀ d' ∈ ords, 1 ≤ d') {k : ℤ} (hk : Odd k)
    {d : ℕ} (hd : 1 ≤ d) (I : DerivativeWord2 (d - 1)) (i₀ : Fin 2) (κ : MajConsts)
    {Δ μ₀ : ℝ} (S Kg Kd : ℝ≥0) (hμ : μ₀ ≤ μo v.1) :
    SlotFamRepP D b j₀ G.exports G.level k (oldCtx hcert κ Δ μ₀ S Kg Kd) (fun t A =>
      if hA : IsAdmissibleChain D b j₀ G.level k A then
        fluxCoeff (directFlux G ⟨k, hk⟩ ⟨A, hA⟩ γ ords t) d I 0 i₀ else 0) 0
      (Real.toNNReal |directConst D G.level ords d| *
        ∑ σ : Equiv.Perm (Fin (d - 1)), Real.toNNReal (oldTheta hcert v u γ d (I ∘ σ) i₀)) := by
  have hcont := oldFluxContinuous_of_cert hΛ hζ hb G hcert
  have hrep := famURep_directExpr hζ G ⟨k, hk⟩ γ ords hords hd I i₀
    (fun J c' => oldWrap hcert ⟨v, u, γ, d, J, c', ⟨k, hk⟩⟩)
    (fun J c' => by
      obtain ⟨hs, hf, f, hden, hval⟩ := oldWrap_spec hcert ⟨v, u, γ, d, J, c', ⟨k, hk⟩⟩
      refine ⟨hs, hf, f, hden, fun cc t ht Y z => ?_⟩
      rw [oldFun_flux hcert ⟨v, u, γ, d, J, c', ⟨k, hk⟩⟩ cc t ht Y z]
      split_ifs
      · exact (hval _ _ _).symm
      · rfl)
    (fun _ cc t ht σ => integrableOn_unitCube_of_continuous
      (hcont ⟨k, hk⟩ cc v u γ d (I ∘ σ) t ht))
  obtain ⟨hs, hf, fc, hden, hv⟩ := hrep
  refine ⟨_, hs, hf, ⟨fc, hden, fun A hA t ht => ?_⟩,
    solvedFree_directExpr _ _ _ _ _ _ _ fun J c' => solvedFree_oldWrap hcert _,
    fun t _ mres hmres => ?_⟩
  · simp only [hA, ↓reduceDIte]
    exact (hv (⟨A, hA⟩, t) ht).symm
  · show genNorm D κ Δ (3 * Real.pi * b) (oldLeaf hcert) _ (3 * Real.pi * b) mres 0 t ≤ _
    refine (genNorm_directExpr_le (D := D) κ Δ (3 * Real.pi * b) (oldLeaf hcert)
      (fun s i p e hs => oldLeaf_eq_none_of_ne_ctx hcert e hs) G.level k _ I i₀ _
      (3 * Real.pi * b) mres 0 t).trans ?_
    have hmr : mres ≤ μo v.1 := by
      have h1 : mres + ((0 : ℕ) : ℝ) * Δ ≤ μ₀ := hmres
      simp only [Nat.cast_zero, zero_mul, add_zero] at h1
      exact h1.trans hμ
    rw [ENNReal.coe_mul, ENNReal.ofNNReal_finsetSum]
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun σ _ => ?_)
    exact (genNorm_oldWrap_eq κ Δ (3 * Real.pi * b) hcert _ (3 * Real.pi * b) mres 0 t).trans_le
      (wsum_oldProfile_le hcert hb.le hεn ⟨v, u, γ, d, I ∘ σ, i₀, ⟨k, hk⟩⟩ hmr le_rfl
        (Nat.zero_le _))
end

end AVRegularity.Providers.CascadeInvariants
end
