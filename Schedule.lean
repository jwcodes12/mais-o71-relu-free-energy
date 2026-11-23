import Quantitative

noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal Topology
namespace O71
def scanWidth (n : ℕ) : ℝ := (log n)^(1/3:ℝ)
def resolution (α : ℝ) (n : ℕ) : ℝ := α*(n:ℝ)^(-(1/6):ℝ)

theorem log_scale_limit (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => (log n)^a * (n:ℝ)^(-b)) atTop (𝓝 0) := by
  apply ((isLittleO_log_rpow_rpow_atTop a hb).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  simp [Real.rpow_neg (Nat.cast_nonneg n),div_eq_mul_inv]

theorem normalized_scale {α : ℝ} {n : ℕ} (hn : 0 < n) :
    (n:ℝ)*(resolution α n)^6 = α^6 := by
  rw [resolution,mul_pow,← rpow_mul_natCast (Nat.cast_nonneg n)]
  norm_num [Real.rpow_neg_one]
  field_simp

theorem scanWidth_cube {n : ℕ} (hn : 0 < n) : (scanWidth n)^3 = log n := by
  rw [scanWidth,← rpow_mul_natCast (log_natCast_nonneg n)]; norm_num

theorem schedule_small {α : ℝ} :
    ∀ᶠ n : ℕ in atTop, 1 ≤ scanWidth n ∧ resolution α n ≤ 1/10 ∧ (scanWidth n)^2 * resolution α n ≤ 1/1000 := by
  have hL : Tendsto scanWidth atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hq : Tendsto (resolution α) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => α*(n:ℝ)^(-(1/6):ℝ)) atTop (𝓝 0)
    simpa only [Function.comp_apply,mul_zero] using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)).comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul α
  have hLq : Tendsto (fun n => (scanWidth n)^2 * resolution α n) atTop (𝓝 0) := by
    have h := (log_scale_limit (2/3) (1/6) (by norm_num)).const_mul α
    rw [mul_zero] at h
    apply h.congr'
    filter_upwards with n
    rw [scanWidth, resolution,← rpow_mul_natCast (log_natCast_nonneg n)]
    norm_num
    ring
  filter_upwards [hL.eventually_ge_atTop 1, hq.eventually_le_const (by norm_num : (0:ℝ) < 1/10),
    hLq.eventually_le_const (by norm_num : (0:ℝ) < 1/1000)] with n hl hq he using ⟨hl,hq,he⟩

/-- At these scales all individual exponents are small, even on coincident bumps. -/
theorem schedule_pair (n : ℕ) {q L : ℝ} (hq : 0 < q) (hL : 1 ≤ L)
    (hq1 : q ≤ 1/10) (he : L^2*q ≤ 1/1000) :
    q^2*(1+L) ≤ small ∧ ∀ z ∈ box L ×ˢ box L,
      chartKernel n q z ≤ eexp (n*q^6*(1066*L^3)) ∧
      (2*(1+L)*q^2 < |coordT z.1-coordT z.2| → chartKernel n q z ≤ eexp (n*q^6*99)) := by
  have hL0 := zero_le_one.trans hL
  have hq2 : q ≤ 1 := hq1.trans (by norm_num)
  have hLq : L*q ≤ 1/1000 := (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (L-1)] : L ≤ L^2) hq.le).trans he
  have hJ : 1+L ≤ 2*L := by linarith
  have hA : 7+2*(1+L) ≤ 11*L := by linarith
  have hJq : (1+L)*q ≤ 2/1000 := by linarith [mul_le_mul_of_nonneg_right hJ hq.le]
  have hAq : (7+2*(1+L))*q ≤ 11/1000 := by linarith [mul_le_mul_of_nonneg_right hA hq.le]
  have hA0 : 0 ≤ 7+2*(1+L) := by positivity
  have hqSq : q^2 ≤ 1 := pow_le_one₀ hq.le hq2
  have hd : q^2*(1+L) ≤ small := calc
    _ = ((1+L)*q)*q := by ring
    _ ≤ (2/1000)*1 := mul_le_mul hJq hq2 hq.le (by norm_num)
    _ ≤ _ := by norm_num
  refine ⟨hd,?_⟩
  have ha : 49*q^6 ≤ 1 := by
    have h := pow_le_pow_left₀ hq.le hq1 6
    norm_num at h; linarith
  have hb : (7+2*(1+L))^2*q^4 ≤ 1 := calc
    _ = ((7+2*(1+L))*q)^2*q^2 := by ring
    _ ≤ (11/1000)^2 * (1:ℝ) := mul_le_mul (pow_le_pow_left₀ (by positivity) hAq _) hqSq (sq_nonneg q) (by norm_num)
    _ ≤ _ := by norm_num
  have hbf : 7*(7+2*(1+L))*q^5 ≤ 1 := calc
    _ = 7*(((7+2*(1+L))*q)*q^4) := by ring
    _ ≤ 7*((11/1000)*1) := by gcongr; exact pow_le_one₀ hq.le hq2
    _ ≤ _ := by norm_num
  have hcross : 28*(7+2*(1+L))*(1+L)*q ≤ 1 := calc
    _ ≤ 28*(11*L)*(2*L)*q := by gcongr
    _ = 616*(L^2*q) := by ring
    _ ≤ 616*(1/1000) := by gcongr
    _ ≤ _ := by norm_num
  intro z hz
  have h := quantitative_pair n (zero_lt_one.trans_le hL) hq hq2 hd ha hb hbf hcross z hz
  refine ⟨h.1.trans (ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_)), h.2⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hh : 4*(7+2*(1+L))^2*(1+L) ≤ 4*(11*L)^2*(2*L) := by gcongr
  have hh' : (1:ℝ) ≤ L^3 := one_le_pow₀ hL
  linarith
end O71
