import Likelihood

noncomputable section
open MeasureTheory Set ProbabilityTheory Real Filter
open scoped ENNReal
namespace O71
variable {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
def mixture {n : ℕ} (f : Θ → ℝ → ℝ) (s : Sample n) := ∫⁻ w, likelihood (f w) s ∂ν

theorem likelihood_joint {n : ℕ} {f : Θ → ℝ → ℝ} (hf : Measurable f.uncurry) :
    Measurable (fun z : Sample n × Θ => likelihood (f z.2) z.1) := by
  unfold likelihood ratio eexp
  have hm (i : Fin n) : Measurable (fun z : Sample n × Θ => f z.2 (z.1 i).1) :=
    hf.comp (measurable_snd.prodMk (by fun_prop))
  fun_prop

theorem mixture_mean {n : ℕ} {f : Θ → ℝ → ℝ} (hf : Measurable f.uncurry) :
    ∫⁻ s : Sample n, mixture ν f s ∂sampleLaw n = 1 := by
  unfold mixture
  rw [lintegral_lintegral_swap (likelihood_joint (n := n) (f := f) hf).aemeasurable]
  have h (w : Θ) := likelihood_mean (n := n) (f := f w) (hf.of_uncurry_left)
  simp_rw [h]
  simp

theorem mixture_square_point {n : ℕ} {f : Θ → ℝ → ℝ} (hf : Measurable f.uncurry) (s : Sample n) :
    (mixture ν f s)^2 = ∫⁻ z : Θ × Θ, likelihood (f z.1) s * likelihood (f z.2) s ∂ν.prod ν := by
  have hw : Measurable (fun w => likelihood (f w) s) := by
    have hm (i : Fin n) : Measurable (fun w => f w (s i).1) := hf.of_uncurry_right
    unfold likelihood ratio eexp
    fun_prop
  rw [pow_two]
  exact (lintegral_prod_mul (μ := ν) (ν := ν) hw.aemeasurable hw.aemeasurable).symm

theorem pair_joint {n : ℕ} {f : Θ → ℝ → ℝ} (hf : Measurable f.uncurry) :
    Measurable (fun z : Sample n × (Θ × Θ) => likelihood (f z.2.1) z.1 * likelihood (f z.2.2) z.1) := by
  have hm₁ (i : Fin n) : Measurable (fun z : Sample n × (Θ × Θ) => f z.2.1 (z.1 i).1) :=
    hf.comp (show Measurable (fun z : Sample n × (Θ × Θ) => (z.2.1,(z.1 i).1)) by fun_prop)
  have hm₂ (i : Fin n) : Measurable (fun z : Sample n × (Θ × Θ) => f z.2.2 (z.1 i).1) :=
    hf.comp (show Measurable (fun z : Sample n × (Θ × Θ) => (z.2.2,(z.1 i).1)) by fun_prop)
  unfold likelihood ratio eexp; fun_prop

theorem mixture_square {n : ℕ} {f : Θ → ℝ → ℝ} (hf : Measurable f.uncurry) :
    ∫⁻ s : Sample n, (mixture ν f s)^2 ∂sampleLaw n =
    ∫⁻ z : Θ × Θ, (∫⁻ x, eexp (f z.1 x*f z.2 x) ∂inputLaw)^n ∂ν.prod ν := by
  calc
    _ = ∫⁻ s : Sample n, ∫⁻ z : Θ × Θ, likelihood (f z.1) s * likelihood (f z.2) s ∂ν.prod ν ∂sampleLaw n :=
      lintegral_congr (mixture_square_point ν hf)
    _ = ∫⁻ z : Θ × Θ, ∫⁻ s : Sample n, likelihood (f z.1) s * likelihood (f z.2) s ∂sampleLaw n ∂ν.prod ν :=
      lintegral_lintegral_swap (pair_joint (n := n) hf).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      exact likelihood_pair (n := n) (f := f z.1) (g := f z.2) hf.of_uncurry_left hf.of_uncurry_left

/-- An elementary uniform positive lower-tail probability using truncation at 4B. -/
theorem positive_probability {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ≥0∞} {B : ℝ} (hB : 0 < B) (hm : Measurable Y) (hmean : ∫⁻ x, Y x ∂μ = 1)
    (hsecond : ∫⁻ x, (Y x)^2 ∂μ ≤ ENNReal.ofReal B) :
    1/(16*B) ≤ μ.real {x | 1/2 ≤ (Y x).toReal} := by
  let A := {x | 1/2 ≤ (Y x).toReal}
  have hmA : MeasurableSet A := measurableSet_le measurable_const hm.ennreal_toReal
  have hfin : (∫⁻ x, Y x ∂μ) ≠ ∞ := by simp [hmean]
  have hfin₂ : (∫⁻ x, Y x^2 ∂μ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsecond
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin
  have h₂ := integrable_toReal_of_lintegral_ne_top (hm.pow_const 2).aemeasurable hfin₂
  simp only [ENNReal.toReal_pow] at h₂
  have hmean' := integral_toReal hm.aemeasurable (ae_lt_top hm hfin)
  rw [hmean,ENNReal.toReal_one] at hmean'
  have hsq := integral_toReal (hm.pow_const 2).aemeasurable (ae_lt_top (hm.pow_const 2) hfin₂)
  simp only [ENNReal.toReal_pow] at hsq
  have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsecond
  rw [ENNReal.toReal_ofReal hB.le,← hsq] at hu
  have h := integral_mono (μ := μ) hi ((integrable_const (1/2:ℝ)).add
    ((integrable_const (4*B)).indicator hmA) |>.add (h₂.div_const (4*B))) (fun x => by
      change (Y x).toReal ≤ 1/2 + A.indicator (fun _ => 4*B) x + (Y x).toReal^2/(4*B)
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx]
        have ht : 0 < 4*B := by positivity
        by_cases hsmall : (Y x).toReal ≤ 4*B
        · linarith [div_nonneg (sq_nonneg (Y x).toReal) ht.le]
        · have H : (Y x).toReal ≤ (Y x).toReal^2/(4*B) := (le_div_iff₀ ht).mpr
            (by nlinarith [mul_nonneg (Y x).toReal_nonneg (sub_nonneg.mpr (le_of_not_ge hsmall))])
          linarith
      · rw [indicator_of_notMem hx,add_zero]
        change ¬1/2 ≤ (Y x).toReal at hx
        linarith [div_nonneg (sq_nonneg (Y x).toReal) (by positivity : 0 ≤ 4*B)])
  rw [integral_add' ((integrable_const (1/2:ℝ)).add ((integrable_const (4*B)).indicator hmA)) (h₂.div_const (4*B)),
    integral_add' (integrable_const (1/2:ℝ)) ((integrable_const (4*B)).indicator hmA),integral_div,
    integral_indicator_const _ hmA,integral_const,hmean'] at h
  simp only [integral_div,probReal_univ,one_smul,smul_eq_mul] at h
  have hdiv : (∫ x, (Y x).toReal^2 ∂μ)/(4*B) ≤ 1/4 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  apply (div_le_iff₀ (by positivity)).mpr
  change 1 ≤ μ.real A * (16*B)
  nlinarith only [h,hdiv]
end O71
