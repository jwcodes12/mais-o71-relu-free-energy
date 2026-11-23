import TheoremA

noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
namespace O71

private def rate (a k t : ℝ) := exp (-a*t)*t^k

private theorem rate_div {t : ℝ} (ht : 0 < t) (a b k l : ℝ) :
    rate b l t / rate a k t = t^(l-k)*exp (-(b-a)*t) := by
  unfold rate
  rw [Real.rpow_sub ht,show -(b-a)*t = (-b*t)-(-a*t) by ring,Real.exp_sub]
  ring

private theorem vanishing_ratio {F : ℝ → ℝ} {a b k l U V : ℝ}
    (hU : Tendsto (fun t => F t / rate a k t) atTop (𝓝 U))
    (hV : Tendsto (fun t => F t / rate b l t) atTop (𝓝 V))
    (hr : Tendsto (fun t => rate b l t / rate a k t) atTop (𝓝 0)) : U = 0 := by
  have h := hV.mul hr
  rw [mul_zero] at h
  exact tendsto_nhds_unique hU (h.congr' (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have hn : rate b l t ≠ 0 := mul_ne_zero (exp_pos _).ne' (rpow_pos_of_pos ht _).ne'
    field_simp))

private theorem smaller_rate {a b : ℝ} (hab : a < b) (k l : ℝ) :
    Tendsto (fun t => rate b l t / rate a k t) atTop (𝓝 0) := by
  apply (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (l-k) (b-a) (sub_pos.mpr hab)).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht using (rate_div ht ..).symm

/-- Uniqueness among all positive-constant, power-log forms in Display 1. -/
theorem display_one_unique (a C : ℝ) (m : ℕ) (hm : 1 ≤ m) (hC : 0 < C)
    (h : Tendsto (fun e : ℝ => (volume (physicalSublevel e)).toReal /
      (e^a * (log (1/e))^(m-1))) (𝓝[>] 0) (𝓝 C)) : a = 11/6 ∧ m = 1 := by
  obtain ⟨U,hU,hlim⟩ := theorem_A
  let F := fun t : ℝ => (volume (physicalSublevel (exp (-t)))).toReal
  have ht : Tendsto (fun t : ℝ => exp (-t)) atTop (𝓝[>] 0) :=
    Real.tendsto_exp_atBot_nhdsGT.comp tendsto_neg_atTop_atBot
  have H : Tendsto (fun t => F t / rate (11/6) 0 t) atTop (𝓝 U) := by
    apply (hlim.comp ht).congr
    intro t
    simp [F,rate,← Real.exp_mul, mul_comm]
  have H' : Tendsto (fun t => F t / rate a ((m-1:ℕ):ℝ) t) atTop (𝓝 C) := by
    apply (h.comp ht).congr
    intro t
    simp [F,rate,← Real.exp_mul,one_div,mul_comm]
  have ha : a = 11/6 := by
    rcases lt_trichotomy a (11/6) with h|h|h
    · exact (hC.ne' (vanishing_ratio H' H (smaller_rate h _ _))).elim
    · exact h
    · exact (hU.ne' (vanishing_ratio H H' (smaller_rate h _ _))).elim
  refine ⟨ha,?_⟩
  by_contra hne
  have hp : (0:ℝ) < ((m-1:ℕ):ℝ) := by exact_mod_cast (show 0 < m-1 by omega)
  rw [ha] at H'
  apply hC.ne'
  apply vanishing_ratio H' H
  apply (tendsto_rpow_neg_atTop hp).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  simp [rate_div ht]

/-- Uniform probability on the same ball divides the Lebesgue constant by its volume. -/
theorem uniform_prior_asymptotic : ∃ C : ℝ, 0 < C ∧ Tendsto
    (fun e : ℝ => ((volume (physicalSublevel e)).toReal /
      (volume (Metric.closedBall center (1/3))).toReal) / e^(11/6 : ℝ)) (𝓝[>] 0) (𝓝 C) := by
  obtain ⟨C,hC,h⟩ := theorem_A
  let Z := (volume (Metric.closedBall center (1/3))).toReal
  have hZ : 0 < Z := ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (by norm_num)).ne'
    (isCompact_closedBall _ _).measure_ne_top
  refine ⟨C/Z,div_pos hC hZ,(h.div_const Z).congr ?_⟩
  intro e; exact div_right_comm ..

#print axioms display_one_unique
#print axioms uniform_prior_asymptotic
end O71
