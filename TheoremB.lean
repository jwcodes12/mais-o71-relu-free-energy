import Schedule
import Integrated
import Restriction
import PhysicalEvidence
import Refutation

noncomputable section
open MeasureTheory Real Filter ProbabilityTheory Set
open scoped ENNReal Topology
namespace O71

theorem small_scale {η : ℝ} (hη : 0 < η) : ∃ α : ℝ, 0 < α ∧
    1066*α^6 ≤ 1/6 ∧ exp (α^6*99) < 1+η/8 := by
  have h₁ : ∀ᶠ x : ℝ in 𝓝 0, 1066*x^6 < 1/6 :=
    (show Continuous (fun x : ℝ => 1066*x^6) by fun_prop).continuousAt.eventually_lt continuousAt_const (by norm_num)
  have h₂ : ∀ᶠ x : ℝ in 𝓝 0, exp (x^6*99) < 1+η/8 :=
    (show Continuous (fun x : ℝ => exp (x^6*99)) by fun_prop).continuousAt.eventually_lt continuousAt_const (by norm_num; linarith)
  have hxpos : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x := self_mem_nhdsWithin
  obtain ⟨x,hx,h1,h2⟩ := (hxpos.and ((h₁.and h₂).filter_mono
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0))).exists
  exact ⟨x,hx,h1.le,h2⟩

theorem rare_pair_cost {α : ℝ} (hα : 0 < α) (hα' : 1066*α^6 ≤ 1/6) :
    Tendsto (fun n : ℕ => exp (α^6*(1066*(scanWidth n)^3)) *
      (200*(2*(1+scanWidth n)*(resolution α n)^2))) atTop (𝓝 0) := by
  have h := ((log_scale_limit (1/3) (1/6) (by norm_num)).const_mul (800*α^2))
  rw [mul_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards with n
    have hw : 0 ≤ scanWidth n := rpow_nonneg (log_natCast_nonneg n) _
    positivity
  · filter_upwards [schedule_small (α := α),eventually_gt_atTop (0:ℕ)] with n hs hn
    have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
    have hp : exp (α^6*(1066*(scanWidth n)^3)) ≤ (n:ℝ)^(1/6:ℝ) := by
      rw [scanWidth_cube hn, rpow_def_of_pos hn']
      apply exp_le_exp.mpr
      have H := mul_le_mul_of_nonneg_right hα' (log_natCast_nonneg n)
      linarith
    have hj : 1+scanWidth n ≤ 2*scanWidth n := by linarith [hs.1]
    have hprod : (n:ℝ)^(1/6:ℝ)*((n:ℝ)^(-(1/6):ℝ))^2 = (n:ℝ)^(-(1/6):ℝ) := by
      rw [← rpow_mul_natCast hn'.le, ← rpow_add hn']; norm_num
    calc
      _ ≤ (n:ℝ)^(1/6:ℝ)*(200*(2*(2*scanWidth n)*(resolution α n)^2)) := by
        have hw := zero_le_one.trans hs.1
        gcongr
      _ = _ := by
        unfold resolution
        change _ = 800*α^2*(scanWidth n*(n:ℝ)^(-(1/6):ℝ))
        linear_combination 800*α^2*scanWidth n*hprod

/-- Chebyshev's inequality in terms of the uncentered second moment of
a nonnegative mean-one random variable. -/
theorem small_mixture_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ≥0∞} {η : ℝ} (hη : 0 < η) (hm : Measurable Y) (hmean : ∫⁻ x, Y x ∂μ = 1)
    (hsecond : ∫⁻ x, (Y x)^2 ∂μ ≤ ENNReal.ofReal (1+η/4)) :
    μ.real {x | (Y x).toReal < 1/2} ≤ η := by
  have hf : (∫⁻ x, Y x ∂μ) ≠ ∞ := by simp [hmean]
  have hf₂ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsecond
  have hE := integral_toReal hm.aemeasurable (ae_lt_top hm hf)
  rw [hmean,ENNReal.toReal_one] at hE
  have h₂ := integrable_toReal_of_lintegral_ne_top (hm.pow_const 2).aemeasurable hf₂
  simp only [ENNReal.toReal_pow] at h₂
  have hp := (memLp_two_iff_integrable_sq hm.ennreal_toReal.aestronglyMeasurable).mpr h₂
  have hE₂ := integral_toReal (hm.pow_const 2).aemeasurable (ae_lt_top (hm.pow_const 2) hf₂)
  simp only [ENNReal.toReal_pow] at hE₂
  have hV := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsecond
  rw [ENNReal.toReal_ofReal (by positivity),← hE₂] at hV
  have hcheb := meas_ge_le_variance_div_sq hp (by norm_num : 0 < (1/2:ℝ))
  rw [variance_eq_sub hp, hE, one_pow] at hcheb
  have hsub : {x | (Y x).toReal < 1/2} ⊆ {x | 1/2 ≤ |(Y x).toReal-1|} := by
    intro x hx
    change (Y x).toReal < 1/2 at hx
    change 1/2 ≤ |(Y x).toReal-1|
    linarith [neg_le_abs ((Y x).toReal-1)]
  have ha := (measure_mono (μ := μ) hsub).trans hcheb
  have he : μ {x | (Y x).toReal < 1/2} ≤ ENNReal.ofReal η := ha.trans (ENNReal.ofReal_le_ofReal (by
    simp only [Pi.pow_apply]
    have core (v : ℝ) (hv : v ≤ 1+η/4) : (v-1)/(1/2)^2 ≤ η := by norm_num [div_eq_mul_inv] at hv ⊢; linarith only [hv]
    exact core _ hV))
  simpa [measureReal_def,ENNReal.toReal_ofReal hη.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he

/-- Quantitative upper bound on the free-energy remainder for every sufficiently
large sample size under the finite iid uniform-input and Gaussian-noise law. -/
theorem theorem_B : theoremBStatement := by
  intro η hη
  obtain ⟨α,hα,hα',hαη⟩ := small_scale hη
  let K := α^11*small^8/(2*ballMass)
  have hK : 0 < K := by dsimp [K]; positivity [ballMass_pos]
  refine ⟨-log K,?_⟩
  have hc := (rare_pair_cost hα hα').eventually_lt tendsto_const_nhds (by linarith : 0 < η/8)
  filter_upwards [hc,schedule_small (α := α),eventually_gt_atTop (1:ℕ)] with n hcost hs hn
  have hn0 : 0 < n := by omega
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hl : 0 < log n := log_pos (by exact_mod_cast hn)
  let q := resolution α n
  let L := scanWidth n
  have hq : 0 < q := mul_pos hα (rpow_pos_of_pos hn' _)
  have hL : 0 < L := zero_lt_one.trans_le hs.1
  letI : Fact (0 < L) := ⟨hL⟩
  obtain ⟨hbox,hpair⟩ := schedule_pair n hq hs.1 hs.2.1 hs.2.2
  have h2 := box_square_bound n q L _ _ _ hL (by positivity) hpair
  rw [show (n:ℝ)*q^6 = α^6 from normalized_scale hn0] at h2
  let Y := fun s : Sample n => mixture (boxLaw L) (chartNet q) s
  have hm : Measurable Y := (likelihood_joint (n := n) (measurableChartNet q)).lintegral_prod_right'
  have hp := small_mixture_tail hη hm (mixture_mean _ (measurableChartNet _)) (h2.trans (ENNReal.ofReal_le_ofReal (by
    change exp (α^6*99) + exp (α^6*(1066*L^3))*(200*(2*(1+L)*q^2)) ≤ 1+η/4
    linarith)))
  refine (measureReal_mono ?_).trans hp
  intro s hb
  change -log K < residual (11/6) 1 n s + 1/3*log (log n) at hb
  change (Y s).toReal < 1/2
  by_contra! hsY
  have h := restricted_evidence s hq hL (fun w hw => (box_geometry hq (hs.2.1.trans (by norm_num)) hbox hw).1)
  have H := ENNReal.toReal_mono (evidence_finite s) h
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity [ballMass_pos])] at H
  change (q^11*small^8*L/ballMass)*(Y s).toReal ≤ (evidence s).toReal at H
  have he : (q^11*small^8*L/ballMass)/2 ≤ (evidence s).toReal := by
    linarith only [H, mul_le_mul_of_nonneg_left hsY (by positivity [ballMass_pos] : 0 ≤ q^11*small^8*L/ballMass)]
  have hN : 0 < (n:ℝ)^(-(11/6):ℝ) := rpow_pos_of_pos hn' _
  have hfactor : (q^11*small^8*L/ballMass)/2 = K * (n:ℝ)^(-(11/6):ℝ) * L := by
    dsimp only [q,resolution,K]
    rw [mul_pow,←rpow_mul_natCast hn'.le,show -(1/6:ℝ)*(11:ℕ) = -(11/6) by norm_num]
    ring
  rw [hfactor] at he
  have hlog := log_le_log (mul_pos (mul_pos hK hN) hL) he
  rw [log_mul (mul_pos hK hN).ne' hL.ne',log_mul hK.ne' hN.ne',log_rpow hn'] at hlog
  have hwl : log L = (1/3:ℝ)*log (log n) := log_rpow hl _
  rw [hwl] at hlog
  simp only [residual,excess,Nat.sub_self,Nat.cast_zero,zero_mul,add_zero] at hb
  linarith only [hb,hlog]

#print axioms theorem_B
end O71
